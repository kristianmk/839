// law_deep.cpp
//
// Deeper search for configurations of negative reduced cost (see ../law_lp.py for the problem).
// ../law_oracle.cpp only relaxes the positions of given candidates. This program also
// changes the marks: from each start configuration it runs a chain of moves (a double point is
// moved, two simple points are merged, a double point is split), relaxes the positions after
// every move, and accepts a move if the cost goes down, or with the Metropolis probability
// exp(-increase / temperature) if it goes up. It returns the best configurations of each chain.
//
// Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
// AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
// of the author, who is responsible for its content.
//
// Cost of a configuration with n_1 simple points, period N, prices y_1..y_{N-1}:
//
//     n_1 / N - sum_{j=1}^{N-1} y_j |sum_i d_i exp(2 pi i j x_i / N)|^2
//
// This is the reduced cost of the linear programme up to the constant price of the row sum w = 1.
//
// The classes Workspace, ReducedCost and LbfgsMinimizer and the functions dotProduct, addScaled,
// readNumbers, readMarks and logitsFromPositions are those of ../law_oracle.cpp, unchanged; the
// design rules stated there apply here as well. The output carries no proof
// obligation: every law is verified afterwards by law_certify.py and law_check_iv.py.
//
// The chains are reproducible: chain k draws from a generator seeded with (seed, k), so the
// result does not depend on the number of threads.
//
// Input (text):   N minimumGap iterationLimit chainCount stepCount keepCount temperature seed
//                 y_1 .. y_{N-1}
//                 then for each chain:  n / x_1 .. x_n (nondecreasing, in [0, N)) / d_1 .. d_n
// Output (text):  for each chain:  k  (number of configurations kept, at most keepCount)
//                 then k times:  cost n / x_1 .. x_n / d_1 .. d_n

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
#include <random>
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
inline constexpr std::size_t kMaximumChainCount{100000U};
inline constexpr std::size_t kMaximumStepCount{1000000U};
inline constexpr std::size_t kMaximumKeepCount{64U};
inline constexpr std::size_t kMaximumIterationLimit{100000U};
inline constexpr std::size_t kHistoryLength{10U};
inline constexpr std::size_t kLineSearchLimit{40U};
inline constexpr double kArmijoFraction{1.0e-4};
inline constexpr double kSmallestGapExcess{1.0e-6};
inline constexpr double kGradientTolerance{1.0e-22};
inline constexpr double kProgressTolerance{1.0e-13};
inline constexpr double kCurvatureTolerance{1.0e-14};
inline constexpr double kSplitDistance{0.5};
inline constexpr double kSameCostTolerance{1.0e-11};

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

// A periodic configuration: positions in increasing order and marks 1 or 2.
struct Configuration {
    std::vector<double> positions{};
    std::vector<double> marks{};
};

struct Job {
    std::size_t period{};
    double minimumGap{};
    std::size_t iterationLimit{};
    std::size_t stepCount{};
    std::size_t keepCount{};
    double temperature{};
    std::uint64_t seed{};
    std::vector<double> prices{};
    std::vector<Configuration> starts{};
};

struct Kept {
    double cost{};
    Configuration configuration{};
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

[[nodiscard]] double simplePointCount(const std::span<const double> marks) noexcept {
    double count{0.0};
    for (const double mark : marks) {
        if (mark < 1.5) {
            count += 1.0;
        }
    }
    return count;
}

// The moves of the chain. Every move keeps the total multiplicity and the order of the points.
class Mutator {
  public:
    explicit Mutator(const std::size_t capacity) {
        indices_.reserve(capacity);
    }

    // Applies one random move to the configuration. Returns false if no move was possible.
    [[nodiscard]] bool mutate(Configuration& configuration, std::mt19937_64& generator) {
        std::uniform_int_distribution<std::uint32_t> distribution{0U, 9U};
        const std::uint32_t choice{distribution(generator)};
        if (choice < 6U) {
            return moveDouble(configuration, generator);
        }
        if (choice < 8U) {
            return mergeSimplePair(configuration, generator);
        }
        return splitDouble(configuration, generator);
    }

  private:
    // Index of a random element of indices_, or nothing if it is empty.
    [[nodiscard]] std::expected<std::size_t, Error> pick(std::mt19937_64& generator) const {
        if (indices_.empty()) {
            return std::unexpected(Error::InconsistentSizes);
        }
        std::uniform_int_distribution<std::size_t> distribution{0U, indices_.size() - 1U};
        return indices_[distribution(generator)];
    }

    // Two neighbouring simple points become one double point at their midpoint.
    [[nodiscard]] bool mergeSimplePair(Configuration& configuration, std::mt19937_64& generator) {
        const std::size_t pointCount{configuration.positions.size()};
        indices_.clear();
        for (std::size_t i = 0U; (i + 1U) < pointCount; ++i) {
            if ((configuration.marks[i] < 1.5) && (configuration.marks[i + 1U] < 1.5)) {
                indices_.push_back(i);
            }
        }
        const auto picked = pick(generator);
        if (!picked.has_value() || (pointCount < 3U)) {
            return false;
        }
        const std::size_t i{picked.value()};
        configuration.positions[i] = 0.5 * (configuration.positions[i] + configuration.positions[i + 1U]);
        configuration.marks[i] = 2.0;
        const auto offset = static_cast<std::ptrdiff_t>(i + 1U);
        configuration.positions.erase(configuration.positions.begin() + offset);
        configuration.marks.erase(configuration.marks.begin() + offset);
        return true;
    }

    // A double point becomes two simple points, half a unit to each side of it.
    [[nodiscard]] bool splitDouble(Configuration& configuration, std::mt19937_64& generator) {
        const std::size_t pointCount{configuration.positions.size()};
        indices_.clear();
        for (std::size_t i = 0U; i < pointCount; ++i) {
            if (configuration.marks[i] > 1.5) {
                indices_.push_back(i);
            }
        }
        const auto picked = pick(generator);
        if (!picked.has_value() || (configuration.positions.size() >= configuration.positions.capacity())) {
            return false;
        }
        const std::size_t i{picked.value()};
        const double centre{configuration.positions[i]};
        const double lower{(i > 0U) ? configuration.positions[i - 1U] : 0.0};
        const double left{std::max(centre - kSplitDistance, 0.5 * (lower + centre))};
        const double right{centre + kSplitDistance};
        configuration.positions[i] = left;
        configuration.marks[i] = 1.0;
        const auto offset = static_cast<std::ptrdiff_t>(i + 1U);
        configuration.positions.insert(configuration.positions.begin() + offset, right);
        configuration.marks.insert(configuration.marks.begin() + offset, 1.0);
        // keep the order: the new point must not pass its right neighbour
        if (((i + 2U) < configuration.positions.size()) &&
            (configuration.positions[i + 1U] > configuration.positions[i + 2U])) {
            configuration.positions[i + 1U] = 0.5 * (centre + configuration.positions[i + 2U]);
        }
        return true;
    }

    // A double point moves to another place: one double is split and one pair of simple points
    // elsewhere is merged.
    [[nodiscard]] bool moveDouble(Configuration& configuration, std::mt19937_64& generator) {
        if (!mergeSimplePair(configuration, generator)) {
            return false;
        }
        return splitDouble(configuration, generator);
    }

    std::vector<std::size_t> indices_{};
};

// One chain: all the memory it needs is allocated in the constructor.
class ChainRunner {
  public:
    ChainRunner(const std::size_t capacity, const std::size_t iterationLimit, const std::size_t keepCount)
        : capacity_{capacity}, minimizer_{capacity, iterationLimit}, mutator_{capacity} {
        logits_.reserve(capacity);
        current_.positions.reserve(capacity);
        current_.marks.reserve(capacity);
        trial_.positions.reserve(capacity);
        trial_.marks.reserve(capacity);
        kept_.resize(keepCount);
        for (Kept& kept : kept_) {
            kept.configuration.positions.reserve(capacity);
            kept.configuration.marks.reserve(capacity);
        }
    }

    // Runs the chain from the start configuration and writes the best configurations to `result`,
    // whose elements must have the capacity of the period.
    [[nodiscard]] std::expected<std::size_t, Error> run(const Job& job, const ReducedCost& cost,
                                                        const Configuration& start, const std::uint64_t chainIndex,
                                                        const std::span<Kept> result) {
        if ((start.positions.size() > capacity_) || (result.size() != kept_.size())) {
            return std::unexpected(Error::InconsistentSizes);
        }
        std::seed_seq sequence{job.seed, chainIndex};
        std::mt19937_64 generator{sequence};
        std::uniform_real_distribution<double> uniform{0.0, 1.0};
        keptCount_ = 0U;

        current_.positions.assign(start.positions.begin(), start.positions.end());
        current_.marks.assign(start.marks.begin(), start.marks.end());
        const auto startCost = relax(job, cost, current_);
        if (!startCost.has_value()) {
            return std::unexpected(startCost.error());
        }
        double currentCost{startCost.value()};
        remember(currentCost, current_);

        for (std::size_t step = 0U; step < job.stepCount; ++step) {
            trial_.positions.assign(current_.positions.begin(), current_.positions.end());
            trial_.marks.assign(current_.marks.begin(), current_.marks.end());
            if (!mutator_.mutate(trial_, generator)) {
                continue;
            }
            const auto trialCost = relax(job, cost, trial_);
            if (!trialCost.has_value()) {
                if (trialCost.error() == Error::NonFiniteValue) {
                    continue;
                }
                return std::unexpected(trialCost.error());
            }
            const double increase{trialCost.value() - currentCost};
            const bool accepted{(increase <= 0.0) || ((job.temperature > 0.0) &&
                                                      (uniform(generator) < std::exp(-increase / job.temperature)))};
            remember(trialCost.value(), trial_);
            if (accepted) {
                std::swap(current_, trial_);
                currentCost = trialCost.value();
            }
        }
        for (std::size_t k = 0U; k < keptCount_; ++k) {
            result[k].cost = kept_[k].cost;
            result[k].configuration.positions.assign(kept_[k].configuration.positions.begin(),
                                                     kept_[k].configuration.positions.end());
            result[k].configuration.marks.assign(kept_[k].configuration.marks.begin(),
                                                 kept_[k].configuration.marks.end());
        }
        return keptCount_;
    }

  private:
    // Relaxes the positions of the configuration and returns its cost.
    [[nodiscard]] std::expected<double, Error> relax(const Job& job, const ReducedCost& cost,
                                                     Configuration& configuration) {
        const std::size_t pointCount{configuration.positions.size()};
        const double periodLength{static_cast<double>(job.period)};
        if ((pointCount < 2U) || (pointCount > capacity_) || (configuration.marks.size() != pointCount) ||
            !((static_cast<double>(pointCount) * job.minimumGap) < periodLength)) {
            return std::unexpected(Error::InconsistentSizes);
        }
        logits_.assign(pointCount, 0.0); // within the reserved capacity: no allocation
        logitsFromPositions(configuration.positions, periodLength, job.minimumGap, logits_);
        const auto value = minimizer_.minimise(cost, configuration.marks, logits_);
        if (!value.has_value()) {
            return std::unexpected(value.error());
        }
        const std::span<const double> relaxed{minimizer_.positions()};
        if (relaxed.size() != pointCount) {
            return std::unexpected(Error::InconsistentSizes);
        }
        std::ranges::copy(relaxed, configuration.positions.begin());
        return value.value() + (simplePointCount(configuration.marks) / periodLength);
    }

    // Keeps the configuration if it is among the best seen and is not a repetition.
    void remember(const double cost, const Configuration& configuration) {
        for (std::size_t k = 0U; k < keptCount_; ++k) {
            if (std::abs(kept_[k].cost - cost) <= kSameCostTolerance) {
                return;
            }
        }
        std::size_t slot{keptCount_};
        if (keptCount_ < kept_.size()) {
            ++keptCount_;
        } else {
            slot = 0U;
            for (std::size_t k = 1U; k < keptCount_; ++k) {
                if (kept_[k].cost > kept_[slot].cost) {
                    slot = k;
                }
            }
            if ((keptCount_ == 0U) || (kept_[slot].cost <= cost)) {
                return;
            }
        }
        kept_[slot].cost = cost;
        kept_[slot].configuration.positions.assign(configuration.positions.begin(), configuration.positions.end());
        kept_[slot].configuration.marks.assign(configuration.marks.begin(), configuration.marks.end());
    }

    std::size_t capacity_{};
    LbfgsMinimizer minimizer_;
    Mutator mutator_;
    std::vector<double> logits_{};
    Configuration current_{};
    Configuration trial_{};
    std::vector<Kept> kept_{};
    std::size_t keptCount_{};
};

// Reads and validates a job.
[[nodiscard]] std::expected<Job, Error> readJob(std::istream& input) {
    Job job{};
    std::size_t chainCount{0U};
    if (!(input >> job.period >> job.minimumGap >> job.iterationLimit >> chainCount >> job.stepCount >> job.keepCount >>
          job.temperature >> job.seed)) {
        return std::unexpected(Error::MalformedInput);
    }
    if ((job.period < 2U) || !std::isfinite(job.minimumGap) || !(job.minimumGap > 0.0) || (job.iterationLimit < 1U) ||
        (job.keepCount < 1U) || !std::isfinite(job.temperature) || (job.temperature < 0.0)) {
        return std::unexpected(Error::MalformedInput);
    }
    if ((job.period > kMaximumPeriod) || (job.iterationLimit > kMaximumIterationLimit) ||
        (chainCount > kMaximumChainCount) || (job.stepCount > kMaximumStepCount) ||
        (job.keepCount > kMaximumKeepCount)) {
        return std::unexpected(Error::InputTooLarge);
    }
    if (!readNumbers(input, job.period - 1U, job.prices)) {
        return std::unexpected(Error::MalformedInput);
    }
    const double periodLength{static_cast<double>(job.period)};
    job.starts.reserve(chainCount);
    for (std::size_t index = 0U; index < chainCount; ++index) {
        std::size_t pointCount{0U};
        if (!(input >> pointCount) || (pointCount < 2U) || (pointCount > job.period)) {
            return std::unexpected(Error::MalformedInput);
        }
        if (!((static_cast<double>(pointCount) * job.minimumGap) < periodLength)) {
            return std::unexpected(Error::MalformedInput);
        }
        Configuration start{};
        if (!readNumbers(input, pointCount, start.positions) ||
            !readMarks(input, pointCount, job.period, start.marks)) {
            return std::unexpected(Error::MalformedInput);
        }
        double previousPosition{0.0};
        for (const double position : start.positions) {
            if (!(position >= previousPosition) || !(position < periodLength)) {
                return std::unexpected(Error::MalformedInput);
            }
            previousPosition = position;
        }
        job.starts.push_back(std::move(start));
    }
    return job;
}

struct ChainResult {
    std::size_t count{};
    std::vector<Kept> kept{};
};

// Runs all chains. Fails if any chain fails.
[[nodiscard]] std::expected<std::vector<ChainResult>, Error> runAll(const Job& job) {
    const std::size_t chainCount{job.starts.size()};
    std::vector<ChainResult> results(chainCount);
    for (ChainResult& result : results) {
        result.kept.resize(job.keepCount);
        for (Kept& kept : result.kept) {
            kept.configuration.positions.reserve(job.period);
            kept.configuration.marks.reserve(job.period);
        }
    }
    const std::size_t threadCount{maximumThreadCount()};
    std::vector<ChainRunner> runners{};
    runners.reserve(threadCount);
    for (std::size_t thread = 0U; thread < threadCount; ++thread) {
        runners.emplace_back(job.period, job.iterationLimit, job.keepCount);
    }
    const ReducedCost cost{job.period, job.minimumGap, job.prices};
    bool failed{false};
    Error firstError{Error::UnexpectedException};

#pragma omp parallel for schedule(dynamic) default(none)                                                               \
    shared(job, cost, results, runners, failed, firstError, chainCount)
    for (std::size_t index = 0U; index < chainCount; ++index) {
        Error error{Error::UnexpectedException};
        bool succeeded{false};
        try {
            const std::size_t threadIndex{currentThreadIndex()};
            if (threadIndex < runners.size()) {
                const auto outcome = runners[threadIndex].run(job, cost, job.starts[index],
                                                              static_cast<std::uint64_t>(index), results[index].kept);
                succeeded = outcome.has_value();
                if (succeeded) {
                    results[index].count = outcome.value();
                } else {
                    error = outcome.error();
                }
            } else {
                error = Error::OptimizerUnavailable;
            }
        } catch (...) {
            succeeded = false;
        }
        if (!succeeded) {
#pragma omp critical(lawDeepFailure)
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

[[nodiscard]] bool writeResults(std::ostream& output, const std::span<const ChainResult> results) {
    output << std::setprecision(std::numeric_limits<double>::max_digits10);
    for (const ChainResult& result : results) {
        const std::size_t count{std::min(result.count, result.kept.size())};
        output << count << '\n';
        for (std::size_t k = 0U; k < count; ++k) {
            const Kept& kept{result.kept[k]};
            output << kept.cost << ' ' << kept.configuration.positions.size() << '\n';
            for (const double position : kept.configuration.positions) {
                output << position << ' ';
            }
            output << '\n';
            for (const double mark : kept.configuration.marks) {
                output << ((mark > 1.5) ? 2 : 1) << ' ';
            }
            output << '\n';
        }
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
        std::cerr << "usage: law_deep input.txt output.txt\n";
        return ExitCode::UsageError;
    }
    std::ifstream input{arguments[1U]};
    if (!input.is_open()) {
        std::cerr << "law_deep: cannot open the input file\n";
        return ExitCode::InputError;
    }
    const std::expected<Job, Error> job{readJob(input)};
    if (!job.has_value()) {
        std::cerr << "law_deep: " << describe(job.error()) << '\n';
        return ExitCode::InputError;
    }
    const std::expected<std::vector<ChainResult>, Error> results{runAll(job.value())};
    if (!results.has_value()) {
        std::cerr << "law_deep: the search failed: " << describe(results.error()) << '\n';
        return ExitCode::ComputationError;
    }
    std::ofstream output{arguments[2U]};
    if (!output.is_open() || !writeResults(output, results.value())) {
        std::cerr << "law_deep: cannot write the output file\n";
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
        std::cerr << "law_deep: " << error.what() << '\n';
    } catch (...) {
        std::cerr << "law_deep: unknown error\n";
    }
    return static_cast<int>(exitCode);
}
