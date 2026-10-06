// law_oracle.cpp
//
// Local optimisation of periodic marked point configurations. This program is the inner step of
// the column generation in law_cg.py, which searches for a probability law on periodic
// configurations of simple and double points with prescribed pair statistics. See law_lp.py for
// the mathematical problem and README.md for the role of the result.
//
// Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
// AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
// of the author, who is responsible for its content.
//
// Problem solved for each candidate configuration
// -----------------------------------------------
// Given the period N, prices y_1..y_{N-1}, marks d_i in {1, 2} with sum N and start positions,
// minimise over the positions x_i
//
//     G(x) = - sum_{j=1}^{N-1} y_j |sum_i d_i exp(2 pi i j x_i / N)|^2
//
// subject to all gaps, including the gap that closes the period, being at least minimumGap. The
// constraint is built into the parametrisation: gaps = minimumGap + (N - n minimumGap) softmax(u),
// with the first point at 0, because G does not depend on a common shift. The minimiser is L-BFGS
// with a backtracking (Armijo) line search.
//
// The output of this program carries no proof obligation. Every law that is published is verified
// afterwards by law_certify.py and law_check_iv.py in exact and interval arithmetic, and the
// driver recomputes every reduced cost itself.
//
// Input (text):   N minimumGap iterationLimit candidateCount
//                 y_1 .. y_{N-1}
//                 then for each candidate:  n / x_1 .. x_n (nondecreasing, in [0, N)) / d_1 .. d_n
// Output (text):  for each candidate:  G n / x_1 .. x_n
//
// Design rules
// ------------
// * No raw owning pointers, no pointer arithmetic, no C arrays, no C-style casts, no variadic
//   I/O. Storage is std::vector, access is through std::span; the build defines
//   _GLIBCXX_ASSERTIONS, so every element access is bounds-checked.
// * All external input is validated (ranges, finiteness, sizes, consistency) and limited in size
//   before it is used.
// * All memory is allocated before the optimisation starts; the optimisation does not allocate.
// * All loops have explicit bounds; there is no recursion.
// * Every variable is initialised; conversions are explicit; stream states are checked.
// * Errors are values (std::expected); this file contains no throw statement. Exceptions of the
//   standard library (allocation failure) are caught in main and at the boundary of each thread.
// * Threads share only read-only data. Each thread owns its scratch memory and writes only the
//   result slots of the candidates it processes.
//
// Build: see CMakeLists.txt, or
//   g++ -std=c++23 -O2 -march=native -fopenmp -D_GLIBCXX_ASSERTIONS -Wall -Wextra -Wpedantic
//       -Wconversion -Wsign-conversion -Wshadow -Wold-style-cast -Wcast-qual -Wuseless-cast
//       -Wdouble-promotion -Wfloat-equal -Wduplicated-cond -Wlogical-op -Wnull-dereference
//       -Werror -o law_oracle law_oracle.cpp

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numbers>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

namespace law {
namespace {

inline constexpr std::size_t kMaximumPeriod{4096U};
inline constexpr std::size_t kMaximumCandidateCount{100000U};
inline constexpr std::size_t kMaximumTotalPointCount{20000000U};
inline constexpr std::size_t kMaximumIterationLimit{100000U};
inline constexpr std::size_t kHistoryLength{10U};
inline constexpr std::size_t kLineSearchLimit{40U};
inline constexpr double kArmijoFraction{1.0e-4};
inline constexpr double kSmallestGapExcess{1.0e-6};
inline constexpr double kGradientTolerance{1.0e-22};
inline constexpr double kProgressTolerance{1.0e-13};
inline constexpr double kCurvatureTolerance{1.0e-14};

enum class ExitCode : std::uint8_t {
    Success = 0U,
    UsageError = 2U,
    InputError = 3U,
    OutputError = 4U,
    ComputationError = 5U
};

enum class Error : std::uint8_t {
    InconsistentSizes,
    CapacityExceeded,
    NonFiniteValue,
    OptimizerUnavailable,
    MalformedInput,
    InputTooLarge,
    UnexpectedException
};

struct Candidate {
    std::vector<double> positions{};
    std::vector<double> marks{};
};

struct Job {
    std::size_t period{};
    double minimumGap{};
    std::size_t iterationLimit{};
    std::vector<double> prices{};
    std::vector<Candidate> candidates{};
};

struct Result {
    double value{};
    std::vector<double> positions{};
};

// Scratch memory for one evaluation of the cost. The capacity is fixed at construction; setting
// the point count within the capacity does not allocate.
class Workspace {
  public:
    explicit Workspace(const std::size_t capacity) : capacity_{capacity} {
        softmax_.reserve(capacity);
        positions_.reserve(capacity);
        baseReal_.reserve(capacity);
        baseImaginary_.reserve(capacity);
        currentReal_.reserve(capacity);
        currentImaginary_.reserve(capacity);
        positionGradient_.reserve(capacity);
        gapGradient_.reserve(capacity);
    }

    [[nodiscard]] std::expected<void, Error> setPointCount(const std::size_t pointCount) {
        if (pointCount > capacity_) {
            return std::unexpected(Error::CapacityExceeded);
        }
        softmax_.assign(pointCount, 0.0);
        positions_.assign(pointCount, 0.0);
        baseReal_.assign(pointCount, 0.0);
        baseImaginary_.assign(pointCount, 0.0);
        currentReal_.assign(pointCount, 0.0);
        currentImaginary_.assign(pointCount, 0.0);
        positionGradient_.assign(pointCount, 0.0);
        gapGradient_.assign(pointCount, 0.0);
        return {};
    }

    [[nodiscard]] std::size_t pointCount() const noexcept {
        return positions_.size();
    }
    [[nodiscard]] std::span<const double> positions() const noexcept {
        return positions_;
    }
    [[nodiscard]] std::span<double> softmax() noexcept {
        return softmax_;
    }
    [[nodiscard]] std::span<double> mutablePositions() noexcept {
        return positions_;
    }
    [[nodiscard]] std::span<double> baseReal() noexcept {
        return baseReal_;
    }
    [[nodiscard]] std::span<double> baseImaginary() noexcept {
        return baseImaginary_;
    }
    [[nodiscard]] std::span<double> currentReal() noexcept {
        return currentReal_;
    }
    [[nodiscard]] std::span<double> currentImaginary() noexcept {
        return currentImaginary_;
    }
    [[nodiscard]] std::span<double> positionGradient() noexcept {
        return positionGradient_;
    }
    [[nodiscard]] std::span<double> gapGradient() noexcept {
        return gapGradient_;
    }

  private:
    std::size_t capacity_{};
    std::vector<double> softmax_{};
    std::vector<double> positions_{};
    std::vector<double> baseReal_{};
    std::vector<double> baseImaginary_{};
    std::vector<double> currentReal_{};
    std::vector<double> currentImaginary_{};
    std::vector<double> positionGradient_{};
    std::vector<double> gapGradient_{};
};

[[nodiscard]] double dotProduct(const std::span<const double> left, const std::span<const double> right) noexcept {
    const std::size_t count{std::min(left.size(), right.size())};
    double sum{0.0};
    for (std::size_t k = 0U; k < count; ++k) {
        sum += left[k] * right[k];
    }
    return sum;
}

void addScaled(const std::span<double> target, const double scale, const std::span<const double> source) noexcept {
    const std::size_t count{std::min(target.size(), source.size())};
    for (std::size_t k = 0U; k < count; ++k) {
        target[k] += scale * source[k];
    }
}

// The function G in the softmax parametrisation of the gaps. The prices must outlive this object.
class ReducedCost {
  public:
    ReducedCost(const std::size_t period, const double minimumGap, const std::span<const double> prices) noexcept
        : period_{period}, minimumGap_{minimumGap}, prices_{prices} {}

    // Returns G and writes its gradient with respect to the logits. After a successful call,
    // workspace.positions() holds the positions that belong to the logits.
    [[nodiscard]] std::expected<double, Error> evaluate(const std::span<const double> marks,
                                                        const std::span<const double> logits,
                                                        const std::span<double> gradient,
                                                        Workspace& workspace) const noexcept {
        const std::size_t pointCount{logits.size()};
        if ((period_ < 2U) || (prices_.size() != (period_ - 1U)) || (pointCount < 2U) || (marks.size() != pointCount) ||
            (gradient.size() != pointCount) || (workspace.pointCount() != pointCount)) {
            return std::unexpected(Error::InconsistentSizes);
        }
        // Views of exactly pointCount elements: every access below is bounds-checked against
        // pointCount, and the compiler can see that the loop bounds make the checks redundant.
        const std::span<double> softmax{workspace.softmax().first(pointCount)};
        const std::span<double> positions{workspace.mutablePositions().first(pointCount)};
        const std::span<double> baseReal{workspace.baseReal().first(pointCount)};
        const std::span<double> baseImaginary{workspace.baseImaginary().first(pointCount)};
        const std::span<double> currentReal{workspace.currentReal().first(pointCount)};
        const std::span<double> currentImaginary{workspace.currentImaginary().first(pointCount)};
        const std::span<double> positionGradient{workspace.positionGradient().first(pointCount)};
        const std::span<double> gapGradient{workspace.gapGradient().first(pointCount)};

        const double periodLength{static_cast<double>(period_)};
        const double freeLength{periodLength - (static_cast<double>(pointCount) * minimumGap_)};

        // softmax of the logits, computed relative to the largest one
        const double largestLogit{*std::ranges::max_element(logits)};
        double total{0.0};
        for (std::size_t k = 0U; k < pointCount; ++k) {
            softmax[k] = std::exp(logits[k] - largestLogit);
            total += softmax[k];
        }
        if (!std::isfinite(total) || !(total > 0.0)) {
            return std::unexpected(Error::NonFiniteValue);
        }
        for (std::size_t k = 0U; k < pointCount; ++k) {
            softmax[k] /= total;
        }

        // positions: the first point is at 0, the others follow by the gaps
        positions[0U] = 0.0;
        for (std::size_t k = 1U; k < pointCount; ++k) {
            positions[k] = positions[k - 1U] + minimumGap_ + (freeLength * softmax[k - 1U]);
        }

        const double angularStep{(2.0 * std::numbers::pi) / periodLength};
        for (std::size_t i = 0U; i < pointCount; ++i) {
            baseReal[i] = std::cos(angularStep * positions[i]);
            baseImaginary[i] = std::sin(angularStep * positions[i]);
            currentReal[i] = 1.0;
            currentImaginary[i] = 0.0;
            positionGradient[i] = 0.0;
        }

        // Sum over the frequencies. exp(2 pi i j x / N) is obtained from the previous frequency
        // by one multiplication. The two simd loops have no dependence between iterations: each
        // iteration reads and writes only element i of arrays that do not overlap.
        double value{0.0};
        for (std::size_t frequency = 1U; frequency < period_; ++frequency) {
            double sumReal{0.0};
            double sumImaginary{0.0};
#pragma omp simd reduction(+ : sumReal, sumImaginary)
            for (std::size_t i = 0U; i < pointCount; ++i) {
                const double nextReal{(currentReal[i] * baseReal[i]) - (currentImaginary[i] * baseImaginary[i])};
                const double nextImaginary{(currentReal[i] * baseImaginary[i]) + (currentImaginary[i] * baseReal[i])};
                currentReal[i] = nextReal;
                currentImaginary[i] = nextImaginary;
                sumReal += marks[i] * nextReal;
                sumImaginary += marks[i] * nextImaginary;
            }
            const double price{prices_[frequency - 1U]};
            value -= price * ((sumReal * sumReal) + (sumImaginary * sumImaginary));
            // d|z_j|^2 / dx_i = 2 d_i (2 pi j / N) (Im z_j Re e_ji - Re z_j Im e_ji)
            const double factor{-price * 2.0 * angularStep * static_cast<double>(frequency)};
#pragma omp simd
            for (std::size_t i = 0U; i < pointCount; ++i) {
                positionGradient[i] +=
                    factor * marks[i] * ((sumImaginary * currentReal[i]) - (sumReal * currentImaginary[i]));
            }
        }

        // chain rule: dG/dgap_k = sum_{i > k} dG/dx_i; the gap that closes the period moves no point
        double runningSum{0.0};
        gapGradient[pointCount - 1U] = 0.0;
        for (std::size_t k = pointCount - 1U; k > 0U; --k) {
            runningSum += positionGradient[k];
            gapGradient[k - 1U] = runningSum;
        }
        const double weightedMean{dotProduct(softmax, gapGradient)};
        for (std::size_t k = 0U; k < pointCount; ++k) {
            gradient[k] = freeLength * softmax[k] * (gapGradient[k] - weightedMean);
        }
        if (!std::isfinite(value)) {
            return std::unexpected(Error::NonFiniteValue);
        }
        return value;
    }

  private:
    std::size_t period_{};
    double minimumGap_{};
    std::span<const double> prices_{};
};

// Limited-memory BFGS with a backtracking line search. All storage is allocated in the constructor.
class LbfgsMinimizer {
  public:
    LbfgsMinimizer(const std::size_t capacity, const std::size_t iterationLimit)
        : capacity_{capacity}, iterationLimit_{iterationLimit}, workspace_{capacity} {
        gradient_.reserve(capacity);
        trialGradient_.reserve(capacity);
        trialPoint_.reserve(capacity);
        direction_.reserve(capacity);
        coefficient_.assign(kHistoryLength, 0.0);
        inverseCurvature_.assign(kHistoryLength, 0.0);
        stepHistory_.resize(kHistoryLength);
        gradientHistory_.resize(kHistoryLength);
        for (std::size_t slot = 0U; slot < kHistoryLength; ++slot) {
            stepHistory_[slot].reserve(capacity);
            gradientHistory_[slot].reserve(capacity);
        }
    }

    // Minimises the cost, starting from the given logits, which are overwritten by the final
    // ones. Returns the final value; positions() then holds the final positions.
    [[nodiscard]] std::expected<double, Error> minimise(const ReducedCost& cost, const std::span<const double> marks,
                                                        const std::span<double> logits) {
        const std::size_t pointCount{logits.size()};
        if (pointCount > capacity_) {
            return std::unexpected(Error::CapacityExceeded);
        }
        if (const auto sized = workspace_.setPointCount(pointCount); !sized.has_value()) {
            return std::unexpected(sized.error());
        }
        // within the reserved capacity: no allocation
        gradient_.assign(pointCount, 0.0);
        trialGradient_.assign(pointCount, 0.0);
        trialPoint_.assign(pointCount, 0.0);
        direction_.assign(pointCount, 0.0);
        for (std::size_t slot = 0U; slot < kHistoryLength; ++slot) {
            stepHistory_[slot].assign(pointCount, 0.0);
            gradientHistory_[slot].assign(pointCount, 0.0);
        }

        const auto startValue = cost.evaluate(marks, logits, gradient_, workspace_);
        if (!startValue.has_value()) {
            return std::unexpected(startValue.error());
        }
        double value{startValue.value()};
        std::size_t storedCount{0U};
        std::size_t nextSlot{0U};

        for (std::size_t iteration = 0U; iteration < iterationLimit_; ++iteration) {
            const double gradientSquared{dotProduct(gradient_, gradient_)};
            if (!(gradientSquared >= kGradientTolerance)) {
                break; // stationary point, or a gradient that is not a number
            }
            computeDirection(storedCount, nextSlot);
            double slope{dotProduct(gradient_, direction_)};
            if (!(slope < 0.0)) { // not a descent direction: restart from steepest descent
                for (std::size_t k = 0U; k < pointCount; ++k) {
                    direction_[k] = -gradient_[k];
                }
                slope = -gradientSquared;
                storedCount = 0U;
            }

            double stepLength{(storedCount == 0U) ? std::min(1.0, 1.0 / std::sqrt(gradientSquared)) : 1.0};
            double trialValue{value};
            bool accepted{false};
            for (std::size_t attempt = 0U; attempt < kLineSearchLimit; ++attempt) {
                for (std::size_t k = 0U; k < pointCount; ++k) {
                    trialPoint_[k] = logits[k] + (stepLength * direction_[k]);
                }
                const auto trial = cost.evaluate(marks, trialPoint_, trialGradient_, workspace_);
                if (trial.has_value() && (trial.value() <= (value + (kArmijoFraction * stepLength * slope)))) {
                    trialValue = trial.value();
                    accepted = true;
                    break;
                }
                if (!trial.has_value() && (trial.error() != Error::NonFiniteValue)) {
                    return std::unexpected(trial.error());
                }
                stepLength *= 0.5;
            }
            if (!accepted) {
                break;
            }

            double stepCurvature{0.0};
            const std::span<double> newestStep{stepHistory_[nextSlot]};
            const std::span<double> newestChange{gradientHistory_[nextSlot]};
            for (std::size_t k = 0U; k < pointCount; ++k) {
                newestStep[k] = trialPoint_[k] - logits[k];
                newestChange[k] = trialGradient_[k] - gradient_[k];
                stepCurvature += newestStep[k] * newestChange[k];
            }
            if (stepCurvature > kCurvatureTolerance) {
                inverseCurvature_[nextSlot] = 1.0 / stepCurvature;
                nextSlot = (nextSlot + 1U) % kHistoryLength;
                storedCount = std::min(storedCount + 1U, kHistoryLength);
            }
            std::ranges::copy(trialPoint_, logits.begin());
            std::ranges::copy(trialGradient_, gradient_.begin());
            const double decrease{value - trialValue};
            value = trialValue;
            if (decrease < (kProgressTolerance * (1.0 + std::abs(value)))) {
                break;
            }
        }
        // leave the workspace in the state of the final point
        return cost.evaluate(marks, logits, gradient_, workspace_);
    }

    [[nodiscard]] std::span<const double> positions() const noexcept {
        return workspace_.positions();
    }

  private:
    // Two-loop recursion: direction_ = -H gradient_, with H the L-BFGS approximation of the
    // inverse Hessian built from the stored steps.
    void computeDirection(const std::size_t storedCount, const std::size_t nextSlot) noexcept {
        const std::size_t pointCount{gradient_.size()};
        for (std::size_t k = 0U; k < pointCount; ++k) {
            direction_[k] = -gradient_[k];
        }
        for (std::size_t age = 0U; age < storedCount; ++age) {
            const std::size_t slot{((nextSlot + kHistoryLength) - 1U - age) % kHistoryLength};
            coefficient_[slot] = inverseCurvature_[slot] * dotProduct(stepHistory_[slot], direction_);
            addScaled(direction_, -coefficient_[slot], gradientHistory_[slot]);
        }
        if (storedCount > 0U) {
            const std::size_t newest{((nextSlot + kHistoryLength) - 1U) % kHistoryLength};
            const double curvature{dotProduct(gradientHistory_[newest], gradientHistory_[newest])};
            if (curvature > 0.0) {
                const double scale{dotProduct(stepHistory_[newest], gradientHistory_[newest]) / curvature};
                for (std::size_t k = 0U; k < pointCount; ++k) {
                    direction_[k] *= scale;
                }
            }
        }
        for (std::size_t age = storedCount; age > 0U; --age) {
            const std::size_t slot{((nextSlot + kHistoryLength) - age) % kHistoryLength};
            const double correction{inverseCurvature_[slot] * dotProduct(gradientHistory_[slot], direction_)};
            addScaled(direction_, coefficient_[slot] - correction, stepHistory_[slot]);
        }
    }

    std::size_t capacity_{};
    std::size_t iterationLimit_{};
    Workspace workspace_;
    std::vector<double> gradient_{};
    std::vector<double> trialGradient_{};
    std::vector<double> trialPoint_{};
    std::vector<double> direction_{};
    std::vector<double> coefficient_{};
    std::vector<double> inverseCurvature_{};
    std::vector<std::vector<double>> stepHistory_{};
    std::vector<std::vector<double>> gradientHistory_{};
};

// Reads `count` finite numbers. Returns false if the stream fails or a number is not finite.
[[nodiscard]] bool readNumbers(std::istream& input, const std::size_t count, std::vector<double>& numbers) {
    numbers.assign(count, 0.0);
    for (double& number : numbers) {
        if (!(input >> number) || !std::isfinite(number)) {
            return false;
        }
    }
    return true;
}

// Reads `count` marks, each 1 or 2, and checks that their sum is the period.
[[nodiscard]] bool readMarks(std::istream& input, const std::size_t count, const std::size_t period,
                             std::vector<double>& marks) {
    marks.assign(count, 0.0);
    std::size_t markSum{0U};
    for (double& mark : marks) {
        std::uint32_t markValue{0U};
        if (!(input >> markValue) || ((markValue != 1U) && (markValue != 2U))) {
            return false;
        }
        mark = static_cast<double>(markValue);
        markSum += static_cast<std::size_t>(markValue);
    }
    return markSum == period;
}

// Reads and validates a job.
[[nodiscard]] std::expected<Job, Error> readJob(std::istream& input) {
    Job job{};
    std::size_t candidateCount{0U};
    if (!(input >> job.period >> job.minimumGap >> job.iterationLimit >> candidateCount)) {
        return std::unexpected(Error::MalformedInput);
    }
    if ((job.period < 2U) || !std::isfinite(job.minimumGap) || !(job.minimumGap > 0.0) || (job.iterationLimit < 1U)) {
        return std::unexpected(Error::MalformedInput);
    }
    if ((job.period > kMaximumPeriod) || (job.iterationLimit > kMaximumIterationLimit) ||
        (candidateCount > kMaximumCandidateCount)) {
        return std::unexpected(Error::InputTooLarge);
    }
    if (!readNumbers(input, job.period - 1U, job.prices)) {
        return std::unexpected(Error::MalformedInput);
    }
    const double periodLength{static_cast<double>(job.period)};
    std::size_t totalPointCount{0U};
    job.candidates.reserve(candidateCount);
    for (std::size_t index = 0U; index < candidateCount; ++index) {
        std::size_t pointCount{0U};
        if (!(input >> pointCount) || (pointCount < 2U) || (pointCount > job.period)) {
            return std::unexpected(Error::MalformedInput);
        }
        if (!((static_cast<double>(pointCount) * job.minimumGap) < periodLength)) {
            return std::unexpected(Error::MalformedInput);
        }
        totalPointCount += pointCount;
        if (totalPointCount > kMaximumTotalPointCount) {
            return std::unexpected(Error::InputTooLarge);
        }
        Candidate candidate{};
        if (!readNumbers(input, pointCount, candidate.positions) ||
            !readMarks(input, pointCount, job.period, candidate.marks)) {
            return std::unexpected(Error::MalformedInput);
        }
        double previousPosition{0.0};
        for (const double position : candidate.positions) {
            if (!(position >= previousPosition) || !(position < periodLength)) {
                return std::unexpected(Error::MalformedInput);
            }
            previousPosition = position;
        }
        job.candidates.push_back(std::move(candidate));
    }
    return job;
}

// Start logits from the gaps of the given positions. Gaps below the minimum are raised to it.
void logitsFromPositions(const std::span<const double> positions, const double periodLength, const double minimumGap,
                         const std::span<double> logits) noexcept {
    const std::size_t pointCount{std::min(positions.size(), logits.size())};
    const double freeLength{periodLength - (static_cast<double>(pointCount) * minimumGap)};
    for (std::size_t k = 0U; k < pointCount; ++k) {
        const double nextPosition{((k + 1U) < pointCount) ? positions[k + 1U] : (positions[0U] + periodLength)};
        const double gapExcess{std::max((nextPosition - positions[k]) - minimumGap, kSmallestGapExcess)};
        logits[k] = std::log(gapExcess / freeLength);
    }
}

[[nodiscard]] std::size_t maximumThreadCount() noexcept {
#ifdef _OPENMP
    return static_cast<std::size_t>(std::max(omp_get_max_threads(), 1));
#else
    return 1U;
#endif
}

[[nodiscard]] std::size_t currentThreadIndex() noexcept {
#ifdef _OPENMP
    return static_cast<std::size_t>(std::max(omp_get_thread_num(), 0));
#else
    return 0U;
#endif
}

// Optimises candidates one at a time with its own scratch memory. Each thread has one such object.
class CandidateOptimizer {
  public:
    CandidateOptimizer(const std::size_t capacity, const std::size_t iterationLimit)
        : minimizer_{capacity, iterationLimit} {
        logits_.reserve(capacity);
    }

    [[nodiscard]] std::expected<void, Error> optimise(const Job& job, const ReducedCost& cost,
                                                      const Candidate& candidate, Result& result) {
        const std::size_t pointCount{candidate.positions.size()};
        if ((pointCount > job.period) || (candidate.marks.size() != pointCount) ||
            (result.positions.size() != pointCount)) {
            return std::unexpected(Error::InconsistentSizes);
        }
        logits_.assign(pointCount, 0.0); // within the reserved capacity: no allocation
        logitsFromPositions(candidate.positions, static_cast<double>(job.period), job.minimumGap, logits_);
        const auto value = minimizer_.minimise(cost, candidate.marks, logits_);
        if (!value.has_value()) {
            return std::unexpected(value.error());
        }
        const std::span<const double> finalPositions{minimizer_.positions()};
        if (finalPositions.size() != pointCount) {
            return std::unexpected(Error::InconsistentSizes);
        }
        result.value = value.value();
        std::ranges::copy(finalPositions, result.positions.begin());
        return {};
    }

  private:
    LbfgsMinimizer minimizer_;
    std::vector<double> logits_{};
};

// Optimises all candidates. Fails if any candidate fails.
[[nodiscard]] std::expected<std::vector<Result>, Error> optimiseAll(const Job& job) {
    const std::size_t candidateCount{job.candidates.size()};
    std::vector<Result> results(candidateCount);
    for (std::size_t index = 0U; index < candidateCount; ++index) {
        results[index].positions.assign(job.candidates[index].positions.size(), 0.0);
    }
    const std::size_t threadCount{maximumThreadCount()};
    std::vector<CandidateOptimizer> optimizers{};
    optimizers.reserve(threadCount);
    for (std::size_t thread = 0U; thread < threadCount; ++thread) {
        optimizers.emplace_back(job.period, job.iterationLimit);
    }
    const ReducedCost cost{job.period, job.minimumGap, job.prices};
    bool failed{false};
    Error firstError{Error::UnexpectedException};

#pragma omp parallel for schedule(dynamic) default(none)                                                               \
    shared(job, cost, results, optimizers, failed, firstError, candidateCount)
    for (std::size_t index = 0U; index < candidateCount; ++index) {
        Error error{Error::UnexpectedException};
        bool succeeded{false};
        try {
            const std::size_t threadIndex{currentThreadIndex()};
            if (threadIndex < optimizers.size()) {
                const auto outcome = optimizers[threadIndex].optimise(job, cost, job.candidates[index], results[index]);
                succeeded = outcome.has_value();
                if (!succeeded) {
                    error = outcome.error();
                }
            } else {
                error = Error::OptimizerUnavailable;
            }
        } catch (...) {
            succeeded = false;
        }
        if (!succeeded) {
#pragma omp critical(lawOracleFailure)
            {
                if (!failed) {
                    failed = true;
                    firstError = error;
                }
            }
        }
    }
    if (failed) {
        return std::unexpected(firstError);
    }
    return results;
}

[[nodiscard]] bool writeResults(std::ostream& output, const std::span<const Result> results) {
    output << std::setprecision(std::numeric_limits<double>::max_digits10);
    for (const Result& result : results) {
        output << result.value << ' ' << result.positions.size() << '\n';
        for (const double position : result.positions) {
            output << position << ' ';
        }
        output << '\n';
    }
    output.flush();
    return output.good();
}

[[nodiscard]] std::string_view describe(const Error error) noexcept {
    switch (error) {
    case Error::InconsistentSizes:
        return "inconsistent sizes";
    case Error::CapacityExceeded:
        return "capacity exceeded";
    case Error::NonFiniteValue:
        return "a value is not finite";
    case Error::OptimizerUnavailable:
        return "no scratch memory for a thread";
    case Error::MalformedInput:
        return "the input is malformed";
    case Error::InputTooLarge:
        return "the input exceeds the size limits";
    case Error::UnexpectedException:
        return "unexpected exception";
    }
    return "unknown error";
}

[[nodiscard]] ExitCode run(const std::span<const std::string> arguments) {
    if (arguments.size() != 3U) {
        std::cerr << "usage: law_oracle input.txt output.txt\n";
        return ExitCode::UsageError;
    }
    std::ifstream input{arguments[1U]};
    if (!input.is_open()) {
        std::cerr << "law_oracle: cannot open the input file\n";
        return ExitCode::InputError;
    }
    const std::expected<Job, Error> job{readJob(input)};
    if (!job.has_value()) {
        std::cerr << "law_oracle: " << describe(job.error()) << '\n';
        return ExitCode::InputError;
    }
    const std::expected<std::vector<Result>, Error> results{optimiseAll(job.value())};
    if (!results.has_value()) {
        std::cerr << "law_oracle: the optimisation failed: " << describe(results.error()) << '\n';
        return ExitCode::ComputationError;
    }
    std::ofstream output{arguments[2U]};
    if (!output.is_open() || !writeResults(output, results.value())) {
        std::cerr << "law_oracle: cannot write the output file\n";
        return ExitCode::OutputError;
    }
    return ExitCode::Success;
}

} // namespace
} // namespace law

int main(const int argumentCount, const char* const argumentValues[]) {
    law::ExitCode exitCode{law::ExitCode::ComputationError};
    try {
        const std::span<const char* const> rawArguments{argumentValues,
                                                        static_cast<std::size_t>(std::max(argumentCount, 0))};
        std::vector<std::string> arguments{};
        arguments.reserve(rawArguments.size());
        for (const char* const argument : rawArguments) {
            arguments.emplace_back((argument != nullptr) ? argument : "");
        }
        exitCode = law::run(arguments);
    } catch (const std::exception& error) {
        std::cerr << "law_oracle: " << error.what() << '\n';
    } catch (...) {
        std::cerr << "law_oracle: unknown error\n";
    }
    return static_cast<int>(exitCode);
}
