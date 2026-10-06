// verify.cpp
//
// Reference verifier for the local inequality of the paper (the inequality for consecutive points
// with labels, section "The local inequality"). It decides the inequality for all frames by
// branch and bound over the gaps, in exact integer arithmetic. The number n of points of a frame
// is a compile-time setting, VERIFY_POINT_COUNT: seven by default, and eight for the certificate
// of the critical line. See README.md.
//
// Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
// AI assistance: this file was drafted with AI systems (OpenAI Codex and Claude, Anthropic),
// under the direction of the author, who is responsible for its content.
//
// The proofs of the paper do not depend on this program. The inequality is proved in Lean by a
// checker that is verified there; this program runs the same search outside Lean, and its counts
// of boxes are compared with those of the Lean checker.
//
// What is verified
// ----------------
// A frame is a set of n points y_0 < ... < y_{n-1} with labels d_i in {1, 2} (simple, double) and
// gaps g_r = y_{r+1} - y_r >= theta. With weights W for the n (n - 1) / 2 pairs, rewards kappa for
// the n points, functions B_r of one gap and a rate alpha, the inequality is
//
//     alpha (y_{n-1} - y_0) + sum_{i<j} W_ij^{d_i d_j} K(y_j - y_i)^2
//         + sum_r B_r^{d_r d_{r+1}}(g_r) >= sum_i kappa_{i, d_i}.
//
// Lengths are measured on a grid: one unit of the mean spacing is gridPerUnit grid steps. The
// table (kernel_lower.bin) holds, for each grid cell [k, k+1] with 0 <= k <= gridLength, an
// integer that is at most scale * K(t)^2 for every t in the cell. That property of the table is
// not checked here; it is established when the table is built, and in Lean. Weights, rewards,
// the knot values of the functions B_r (piecewise linear, zero outside the knots) and alpha are
// integers in units of 10^-6. Given the property of the table, a successful run establishes the
// inequality for all real gaps g_r >= minimumGap (in grid steps) and all 2^n labellings. Frames
// with a span beyond gridLength need no table: a condition on the data, checked before the
// search, says that alpha times such a span exceeds the largest reward plus the largest value of
// the sum of the -B_r.
//
// A box is a product of n - 1 intervals of gaps. For each box one of the following holds:
//   1. span test:   alpha times the smallest span of the box pays the largest reward and the
//                   largest value of the sum of the -B_r;
//   2. basic test:  the range minima of the table over the pair distances, the minima of the
//                   functions B_r over the gap intervals and a bound for the labels suffice;
//   3. affine test: on a box of width at most kAffineWidth, lower bounds that are affine in the
//                   gaps are minimised at a corner, for each of the 2^n labellings;
//   4. otherwise the widest interval is halved and both halves are examined.
// The program reports success only when the stack of boxes is empty.
//
// Input:   a parameter file (text, written by make_parameters.py; format in readParameters below)
//          and the table (binary, gridLength + 1 unsigned 32-bit integers, little-endian).
// Output:  one line of JSON with the status and the counts of boxes.
// Exit code: 0 the inequality is verified; 1 a box could not be decided; 2 usage; 3 input
//          rejected; 5 internal limit reached.
//
// Design rules
// ------------
// * No raw owning pointers, no pointer arithmetic, no C arrays, no C-style casts, no variadic
//   I/O. Storage is std::array and std::vector; the build defines _GLIBCXX_ASSERTIONS, so every
//   element access is bounds-checked.
// * All external input is validated (format, ranges, sizes, consistency) and limited in size
//   before it is used. The table is decoded byte by byte, independently of the byte order of
//   the machine.
// * All memory is allocated before the search starts; the search does not allocate.
// * All loops have explicit bounds; there is no recursion. The stack of boxes has a fixed
//   capacity, and reaching it is an error.
// * Every variable is initialised; conversions are explicit; stream states are checked.
// * No floating-point arithmetic. All decisions are comparisons of integers.
// * Errors are values (std::expected); this file contains no throw statement. Exceptions of the
//   standard library (allocation failure) are caught in main.
// * Integer ranges. Grid coordinates are 32-bit and values 64-bit. The parameters are limited so
//   that no 32-bit sum of coordinates can overflow, and a bound on the 64-bit intermediates is
//   checked before the search (integerBoundHolds). The sanitizer build traps signed overflow.
// * One compiler extension is used: the 128-bit integer type of GCC and Clang (Wide), for the
//   products in the span test and the affine test, which do not fit in 64 bits. ISO C++23 has no
//   such type.
//
// Build: see CMakeLists.txt, or
//   g++ -std=c++23 -O2 -D_GLIBCXX_ASSERTIONS -Wall -Wextra -Wpedantic -Wconversion
//       -Wsign-conversion -Wshadow -Wold-style-cast -Wcast-qual -Wuseless-cast -Wduplicated-cond
//       -Wlogical-op -Wnull-dereference -Werror -o verify verify.cpp
// and with -DVERIFY_POINT_COUNT=8 -o verify8 for frames of eight points.

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <fstream>
#include <iostream>
#include <istream>
#include <limits>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace certificate {
namespace {

// Coordinates on the grid, exact values, and the wide type for products of two values.
using Grid = std::int32_t;
using Value = std::int64_t;
__extension__ using Wide = __int128;

// The number of points of a frame: seven in the first and third certificate of the paper, eight
// in the second (the certificate of the critical line).
#ifdef VERIFY_POINT_COUNT
inline constexpr std::size_t kPointCount{VERIFY_POINT_COUNT};
#else
inline constexpr std::size_t kPointCount{7U};
#endif
static_assert((kPointCount >= 3U) && (kPointCount <= 10U), "a frame has between three and ten points");
inline constexpr std::size_t kGapCount{kPointCount - 1U};
inline constexpr std::size_t kPairCount{(kPointCount * (kPointCount - 1U)) / 2U};
inline constexpr std::size_t kPairTypeCount{3U};
inline constexpr std::size_t kLabelCount{2U};
inline constexpr std::size_t kKnotCount{14U};
inline constexpr std::size_t kLabellingCount{std::size_t{1} << kPointCount};
inline constexpr std::size_t kStackCapacity{240U};
inline constexpr Grid kAffineWidth{512};
inline constexpr std::uint64_t kProgressInterval{50000000U};

// Limits on the input.
inline constexpr Grid kMaximumGridLength{1 << 21};
inline constexpr Grid kMaximumGridPerUnit{1 << 20};
inline constexpr Value kMaximumScale{Value{1} << 30};
inline constexpr Value kMaximumMagnitude{1000000000};
inline constexpr Grid kMaximumKnotPosition{1 << 26};

// The condition on the weights of the paper, sum over the pairs (i, i+s) at most 2 d d', in
// units of 10^-6, for the pair types (1,1), (1,2), (2,2).
inline constexpr std::array<Value, kPairTypeCount> kWeightCaps{2000000, 4000000, 8000000};

static_assert(sizeof(Wide) == 16U, "a 128-bit integer type is required");
static_assert(kPairCount == (kPointCount * (kPointCount - 1U)) / 2U);
static_assert(kGapCount == kPointCount - 1U);
static_assert(kLabellingCount == (std::size_t{1} << kPointCount));

enum class ExitCode : std::uint8_t { Success = 0U, Unresolved = 1U, UsageError = 2U, InputError = 3U, LimitError = 5U };

enum class Error : std::uint8_t {
    MalformedParameters,
    ParameterOutOfRange,
    ConditionViolated,
    IntegerBoundExceeded,
    MalformedTable,
    TableEntryTooLarge,
    Unresolved,
    StackExhausted
};

using PairWeights = std::array<std::array<Value, kPairCount>, kPairTypeCount>;
using Rewards = std::array<std::array<Value, kPointCount>, kLabelCount>;
using PotentialKnots = std::array<std::array<std::array<Value, kKnotCount>, kPairTypeCount>, kGapCount>;
using GapArray = std::array<Grid, kGapCount>;

// The frozen data of a certificate, as read from the parameter file.
struct Parameters {
    Grid gridLength{};  // R: index of the last cell of the table; gaps are searched up to R
    Grid gridPerUnit{}; // grid steps per unit length
    Value scale{};      // the table holds lower bounds for scale * K^2
    Value alpha{};      // the rate alpha, in units of 10^-6 per unit length
    Grid minimumGap{};  // the separation theta, in grid steps, rounded down
    Grid firstKnot{};   // position of the first knot of the functions B_r, in grid steps
    Grid knotStep{};    // distance between knots, in grid steps
    PairWeights weights{};
    Rewards rewards{};
    PotentialKnots potentials{};
};

// The pairs (i, j), i < j, in the order of the parameter file.
struct PairIndex {
    std::array<std::size_t, kPairCount> first{};
    std::array<std::size_t, kPairCount> second{};
};

[[nodiscard]] constexpr PairIndex makePairIndex() noexcept {
    PairIndex pairs{};
    std::size_t pair{0U};
    for (std::size_t first = 0U; first < kPointCount; ++first) {
        for (std::size_t second = first + 1U; second < kPointCount; ++second) {
            pairs.first[pair] = first;
            pairs.second[pair] = second;
            ++pair;
        }
    }
    return pairs;
}

inline constexpr PairIndex kPairs{makePairIndex()};

[[nodiscard]] constexpr std::size_t toIndex(const Grid coordinate) noexcept {
    return static_cast<std::size_t>(coordinate);
}

// Quantities derived from the parameters, and the tables for the labellings.
struct Certificate {
    Parameters parameters{};
    Value rewardSumSimple{};  // h1: sum of the rewards of the points of a frame, all simple
    Value rewardSumDouble{};  // h2: sum of the rewards of the points of a frame, all double
    Value potentialBudget{};  // sum over the gaps of the largest value of -B_r
    Value pressure{};         // alpha per grid step, times scale
    Value scalePerKnotStep{}; // scale / knotStep
    Grid lastKnot{};
    std::array<std::array<std::size_t, kPairCount>, kLabellingCount> pairType{};
    std::array<std::array<std::size_t, kGapCount>, kLabellingCount> gapType{};
    std::array<Value, kLabellingCount> rightSide{}; // twice the reward of the labelling, times scale
};

[[nodiscard]] bool readKeyword(std::istream& input, const std::string_view keyword) {
    std::string word{};
    return static_cast<bool>(input >> word) && (word == keyword);
}

[[nodiscard]] bool readValue(std::istream& input, Value& value) {
    return static_cast<bool>(input >> value);
}

[[nodiscard]] bool readNamedValue(std::istream& input, const std::string_view keyword, Value& value) {
    return readKeyword(input, keyword) && readValue(input, value);
}

[[nodiscard]] bool readValues(std::istream& input, const std::span<Value> values) {
    bool complete{true};
    for (Value& value : values) {
        complete = complete && readValue(input, value);
    }
    return complete;
}

[[nodiscard]] constexpr bool withinGridLimit(const Value value, const Grid lowest, const Grid highest) noexcept {
    return (value >= Value{lowest}) && (value <= Value{highest});
}

// Reads the parameter file. Format (tokens separated by white space, in this order):
//   certificate-parameters 1
//   gridLength R   gridPerUnit G   scale S   alpha A   minimumGap M   firstKnot K0   knotStep KS
//   weights      3 x n (n - 1) / 2 integers: pair types (1,1), (1,2), (2,2); pairs (0,1), (0,2),
//                ..., (n - 2, n - 1)
//   rewards      2 x n integers: simple points, double points
//   potentials   (n - 1) x 3 x 14 integers: gap, pair type, knot
//   end
// Only the format and the sizes are checked here; the conditions are checked in makeCertificate.
[[nodiscard]] std::expected<Parameters, Error> readParameters(std::istream& input) {
    Value version{0};
    if (!readNamedValue(input, "certificate-parameters", version) || (version != 1)) {
        return std::unexpected(Error::MalformedParameters);
    }
    Value gridLength{0};
    Value gridPerUnit{0};
    Value scale{0};
    Value alpha{0};
    Value minimumGap{0};
    Value firstKnot{0};
    Value knotStep{0};
    if (!readNamedValue(input, "gridLength", gridLength) || !readNamedValue(input, "gridPerUnit", gridPerUnit) ||
        !readNamedValue(input, "scale", scale) || !readNamedValue(input, "alpha", alpha) ||
        !readNamedValue(input, "minimumGap", minimumGap) || !readNamedValue(input, "firstKnot", firstKnot) ||
        !readNamedValue(input, "knotStep", knotStep)) {
        return std::unexpected(Error::MalformedParameters);
    }
    if (!withinGridLimit(gridLength, 1, kMaximumGridLength) || !withinGridLimit(gridPerUnit, 1, kMaximumGridPerUnit) ||
        (scale < 1) || (scale > kMaximumScale) || (alpha < 0) || (alpha > kMaximumMagnitude) ||
        !withinGridLimit(minimumGap, 1, kMaximumGridLength) || !withinGridLimit(firstKnot, 0, kMaximumKnotPosition) ||
        !withinGridLimit(knotStep, 1, kMaximumKnotPosition)) {
        return std::unexpected(Error::ParameterOutOfRange);
    }
    Parameters parameters{};
    parameters.gridLength = static_cast<Grid>(gridLength);
    parameters.gridPerUnit = static_cast<Grid>(gridPerUnit);
    parameters.scale = scale;
    parameters.alpha = alpha;
    parameters.minimumGap = static_cast<Grid>(minimumGap);
    parameters.firstKnot = static_cast<Grid>(firstKnot);
    parameters.knotStep = static_cast<Grid>(knotStep);
    if (!readKeyword(input, "weights")) {
        return std::unexpected(Error::MalformedParameters);
    }
    for (std::array<Value, kPairCount>& row : parameters.weights) {
        if (!readValues(input, row)) {
            return std::unexpected(Error::MalformedParameters);
        }
    }
    if (!readKeyword(input, "rewards")) {
        return std::unexpected(Error::MalformedParameters);
    }
    for (std::array<Value, kPointCount>& row : parameters.rewards) {
        if (!readValues(input, row)) {
            return std::unexpected(Error::MalformedParameters);
        }
    }
    if (!readKeyword(input, "potentials")) {
        return std::unexpected(Error::MalformedParameters);
    }
    for (std::array<std::array<Value, kKnotCount>, kPairTypeCount>& gap : parameters.potentials) {
        for (std::array<Value, kKnotCount>& row : gap) {
            if (!readValues(input, row)) {
                return std::unexpected(Error::MalformedParameters);
            }
        }
    }
    std::string rest{};
    if (!readKeyword(input, "end") || static_cast<bool>(input >> rest)) {
        return std::unexpected(Error::MalformedParameters);
    }
    return parameters;
}

[[nodiscard]] constexpr bool magnitudeWithinLimit(const Value value) noexcept {
    return (value >= -kMaximumMagnitude) && (value <= kMaximumMagnitude);
}

[[nodiscard]] bool magnitudesWithinLimit(const Parameters& parameters) noexcept {
    for (const std::array<Value, kPairCount>& row : parameters.weights) {
        if (!std::ranges::all_of(row, magnitudeWithinLimit)) {
            return false;
        }
    }
    for (const std::array<Value, kPointCount>& row : parameters.rewards) {
        if (!std::ranges::all_of(row, magnitudeWithinLimit)) {
            return false;
        }
    }
    for (const std::array<std::array<Value, kKnotCount>, kPairTypeCount>& gap : parameters.potentials) {
        for (const std::array<Value, kKnotCount>& row : gap) {
            if (!std::ranges::all_of(row, magnitudeWithinLimit)) {
                return false;
            }
        }
    }
    return true;
}

// The conditions on local data: rewards 0 <= kappa_1 <= kappa_2; weights nonnegative, increasing
// with the labels, and within the caps for every distance of indices; the functions B_r sum to
// zero over r at every knot. The functions B_r must also vanish at their first and last knot:
// they are zero outside the knots, and the search uses that a continuous piecewise linear
// function takes its minimum over an interval at an end point or at a knot.
[[nodiscard]] bool conditionsHold(const Parameters& parameters) noexcept {
    for (std::size_t point = 0U; point < kPointCount; ++point) {
        if ((parameters.rewards[0U][point] < 0) || (parameters.rewards[1U][point] < parameters.rewards[0U][point])) {
            return false;
        }
    }
    for (std::size_t type = 0U; type < kPairTypeCount; ++type) {
        for (std::size_t distance = 1U; distance < kPointCount; ++distance) {
            Value sum{0};
            for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
                if (parameters.weights[type][pair] < 0) {
                    return false;
                }
                if ((kPairs.second[pair] - kPairs.first[pair]) == distance) {
                    sum += parameters.weights[type][pair];
                }
            }
            if (sum > kWeightCaps[type]) {
                return false;
            }
        }
    }
    for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
        if ((parameters.weights[1U][pair] < parameters.weights[0U][pair]) ||
            (parameters.weights[2U][pair] < parameters.weights[0U][pair])) {
            return false;
        }
    }
    for (std::size_t type = 0U; type < kPairTypeCount; ++type) {
        for (std::size_t knot = 0U; knot < kKnotCount; ++knot) {
            Value sum{0};
            for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
                sum += parameters.potentials[gap][type][knot];
            }
            if (sum != 0) {
                return false;
            }
        }
    }
    for (const std::array<std::array<Value, kKnotCount>, kPairTypeCount>& gap : parameters.potentials) {
        for (const std::array<Value, kKnotCount>& row : gap) {
            if ((row.front() != 0) || (row.back() != 0)) {
                return false;
            }
        }
    }
    return true;
}

// A bound for the 64-bit intermediates of the search: the largest weight, knot value and reward,
// the rate and the length of the grid enter it. The largest intermediate of the basic test is
// twice its bound plus the penalty of the labels. For frames of n points, with W, B and h the
// largest weight, knot value and reward, its absolute value is at most
//     2 pressure gridLength + scale (3 n (n - 1) W + (4 n + 2) (n - 1) B + 4 n h),
// and the three factors are at most 512 for n <= 10 (the middle one is the largest).
static_assert((((4U * kPointCount) + 2U) * (kPointCount - 1U)) <= 512U);
[[nodiscard]] bool integerBoundHolds(const Parameters& parameters) noexcept {
    Value largestWeight{0};
    Value largestKnot{0};
    Value largestReward{0};
    for (const std::array<Value, kPairCount>& row : parameters.weights) {
        largestWeight = std::max(largestWeight, std::ranges::max(row));
    }
    for (const std::array<std::array<Value, kKnotCount>, kPairTypeCount>& gap : parameters.potentials) {
        for (const std::array<Value, kKnotCount>& row : gap) {
            for (const Value value : row) {
                largestKnot = std::max(largestKnot, (value < 0) ? -value : value);
            }
        }
    }
    largestReward = std::max(largestReward, std::ranges::max(parameters.rewards[1U]));
    const Value scale{parameters.scale};
    const Value gridLength{parameters.gridLength};
    const Wide searchBound{(Wide{512} * scale * (largestWeight + largestKnot + largestReward)) +
                           (Wide{64} * parameters.alpha * (scale / parameters.gridPerUnit) * (gridLength + 2))};
    const Wide supportBound{(Wide{4} * scale * (gridLength + 2)) +
                            (Wide{4} * largestKnot * scale * (1 + (gridLength / parameters.knotStep)))};
    return std::max(searchBound, supportBound) < Wide{std::numeric_limits<Value>::max()};
}

// Validates the parameters and derives the quantities used by the search.
[[nodiscard]] std::expected<Certificate, Error> makeCertificate(const Parameters& parameters) {
    if (!magnitudesWithinLimit(parameters) || (parameters.minimumGap > parameters.gridLength) ||
        ((Value{parameters.firstKnot} + (Value{kKnotCount - 1U} * parameters.knotStep)) > kMaximumKnotPosition)) {
        return std::unexpected(Error::ParameterOutOfRange);
    }
    if (((parameters.scale % parameters.gridPerUnit) != 0) || ((parameters.scale % parameters.knotStep) != 0) ||
        !conditionsHold(parameters)) {
        return std::unexpected(Error::ConditionViolated);
    }
    Certificate certificate{};
    certificate.parameters = parameters;
    for (std::size_t point = 0U; point < kPointCount; ++point) {
        certificate.rewardSumSimple += parameters.rewards[0U][point];
        certificate.rewardSumDouble += parameters.rewards[1U][point];
    }
    for (const std::array<std::array<Value, kKnotCount>, kPairTypeCount>& gap : parameters.potentials) {
        Value smallest{0};
        for (const std::array<Value, kKnotCount>& row : gap) {
            smallest = std::min(smallest, std::ranges::min(row));
        }
        certificate.potentialBudget -= smallest;
    }
    // The longest span pays the largest reward and the budget of the functions B_r, so the search
    // may stop at gridLength: alpha R >= (h2 + budget) gridPerUnit.
    if ((Wide{parameters.alpha} * parameters.gridLength) <
        (Wide{certificate.rewardSumDouble + certificate.potentialBudget} * parameters.gridPerUnit)) {
        return std::unexpected(Error::ConditionViolated);
    }
    if (!integerBoundHolds(parameters)) {
        return std::unexpected(Error::IntegerBoundExceeded);
    }
    certificate.pressure = parameters.alpha * (parameters.scale / parameters.gridPerUnit);
    certificate.scalePerKnotStep = parameters.scale / parameters.knotStep;
    certificate.lastKnot = parameters.firstKnot + (static_cast<Grid>(kKnotCount - 1U) * parameters.knotStep);
    for (std::size_t labelling = 0U; labelling < kLabellingCount; ++labelling) {
        const auto isDouble = [labelling](const std::size_t point) noexcept -> std::size_t {
            return (labelling >> point) & std::size_t{1};
        };
        Value reward{0};
        for (std::size_t point = 0U; point < kPointCount; ++point) {
            reward += parameters.rewards[isDouble(point)][point];
        }
        certificate.rightSide[labelling] = 2 * reward * parameters.scale;
        for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
            certificate.pairType[labelling][pair] = isDouble(kPairs.first[pair]) + isDouble(kPairs.second[pair]);
        }
        for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
            certificate.gapType[labelling][gap] = isDouble(gap) + isDouble(gap + 1U);
        }
    }
    return certificate;
}

// The table of lower bounds for scale * K^2 on the grid cells, with range minima (sparse table).
class KernelTable {
  public:
    // Reads gridLength + 1 unsigned 32-bit integers, least significant byte first, and nothing
    // else. Every entry must be at most scale.
    [[nodiscard]] static std::expected<KernelTable, Error> read(std::istream& input, const Grid gridLength,
                                                                const Value scale) {
        constexpr std::size_t kBytesPerEntry{4U};
        const std::size_t width{toIndex(gridLength) + 1U};
        std::vector<char> bytes(width * kBytesPerEntry, '\0');
        input.read(bytes.data(), static_cast<std::streamsize>(bytes.size()));
        if (!input.good() || (static_cast<std::size_t>(input.gcount()) != bytes.size()) ||
            (input.peek() != std::istream::traits_type::eof())) {
            return std::unexpected(Error::MalformedTable);
        }
        std::size_t levelCount{1U};
        while ((std::size_t{1} << levelCount) <= width) {
            ++levelCount;
        }
        KernelTable table{};
        table.width_ = width;
        table.minima_.assign(levelCount * width, 0U);
        table.logarithm_.assign(width + 1U, 0U);
        for (std::size_t cell = 0U; cell < width; ++cell) {
            std::uint32_t entry{0U};
            for (std::size_t byte = 0U; byte < kBytesPerEntry; ++byte) {
                const std::uint32_t part{static_cast<unsigned char>(bytes[(cell * kBytesPerEntry) + byte])};
                entry |= part << (8U * byte);
            }
            if (Value{entry} > scale) {
                return std::unexpected(Error::TableEntryTooLarge);
            }
            table.minima_[cell] = entry;
        }
        for (std::size_t length = 2U; length <= width; ++length) {
            table.logarithm_[length] = static_cast<std::uint8_t>(table.logarithm_[length / 2U] + 1U);
        }
        for (std::size_t level = 1U; level < levelCount; ++level) {
            const std::size_t half{std::size_t{1} << (level - 1U)};
            for (std::size_t cell = 0U; (cell + (2U * half)) <= width; ++cell) {
                table.minima_[(level * width) + cell] = std::min(table.minima_[((level - 1U) * width) + cell],
                                                                 table.minima_[((level - 1U) * width) + cell + half]);
            }
        }
        return table;
    }

    // The entry of one cell.
    [[nodiscard]] Value entry(const Grid cell) const noexcept {
        return Value{minima_[toIndex(cell)]};
    }

    // The smallest entry of the cells first, ..., last (first <= last).
    [[nodiscard]] Value minimum(const Grid first, const Grid last) const noexcept {
        const std::size_t level{logarithm_[toIndex(last - first) + 1U]};
        const std::size_t span{std::size_t{1} << level};
        return Value{std::min(minima_[(level * width_) + toIndex(first)],
                              minima_[(level * width_) + toIndex(last) + 1U - span])};
    }

  private:
    KernelTable() = default;

    std::size_t width_{};
    std::vector<std::uint32_t> minima_{};
    std::vector<std::uint8_t> logarithm_{};
};

// A lower bound slope * t + offset.
struct AffineBound {
    Value slope{};
    Value offset{};
};

// The functions B_r of the certificate: continuous, linear between consecutive knots, zero up to
// the first knot and from the last knot on. Values are in units of 10^-6, times scale.
class Potentials {
  public:
    explicit Potentials(const Certificate& certificate) noexcept
        : knots_{certificate.parameters.potentials}, firstKnot_{certificate.parameters.firstKnot},
          knotStep_{certificate.parameters.knotStep}, lastKnot_{certificate.lastKnot},
          scalePerKnotStep_{certificate.scalePerKnotStep} {}

    [[nodiscard]] Value value(const std::size_t gap, const std::size_t type, const Grid position) const noexcept {
        if ((position <= firstKnot_) || (position >= lastKnot_)) {
            return 0;
        }
        const Grid knot{(position - firstKnot_) / knotStep_};
        const Grid remainder{(position - firstKnot_) % knotStep_};
        const std::array<Value, kKnotCount>& knots{knots_[gap][type]};
        return ((knots[toIndex(knot)] * Value{knotStep_ - remainder}) +
                (knots[toIndex(knot) + 1U] * Value{remainder})) *
               scalePerKnotStep_;
    }

    // The smallest value on [lower, upper] of B(type), or of B(type) - B(baseType): a continuous
    // piecewise linear function takes its minimum at an end point or at a knot inside the interval.
    [[nodiscard]] Value minimum(const std::size_t gap, const std::size_t type, const Grid lower,
                                const Grid upper) const noexcept {
        const auto function = [this, gap, type](const Grid position) noexcept { return value(gap, type, position); };
        return minimumOf(function, lower, upper);
    }

    [[nodiscard]] Value minimumOfDifference(const std::size_t gap, const std::size_t type, const std::size_t baseType,
                                            const Grid lower, const Grid upper) const noexcept {
        const auto function = [this, gap, type, baseType](const Grid position) noexcept {
            return value(gap, type, position) - value(gap, baseType, position);
        };
        return minimumOf(function, lower, upper);
    }

    // An affine lower bound on [lower, upper]: the slope at the midpoint, and the largest offset
    // for which the bound holds at the end points and at the knots inside.
    [[nodiscard]] AffineBound affineBound(const std::size_t gap, const std::size_t type, const Grid lower,
                                          const Grid upper) const noexcept {
        const Grid middle{(lower + upper) / 2};
        Value slope{0};
        if ((middle > firstKnot_) && (middle < lastKnot_)) {
            const std::size_t knot{toIndex((middle - firstKnot_) / knotStep_)};
            const std::array<Value, kKnotCount>& knots{knots_[gap][type]};
            slope = (knots[knot + 1U] - knots[knot]) * scalePerKnotStep_;
        }
        const auto function = [this, gap, type, slope](const Grid position) noexcept {
            return value(gap, type, position) - (slope * Value{position});
        };
        return AffineBound{.slope = slope, .offset = minimumOf(function, lower, upper)};
    }

  private:
    template <typename Function>
    [[nodiscard]] Value minimumOf(const Function& function, const Grid lower, const Grid upper) const noexcept {
        Value smallest{std::min(function(lower), function(upper))};
        for (std::size_t knot = 0U; knot < kKnotCount; ++knot) {
            const Grid position{firstKnot_ + (static_cast<Grid>(knot) * knotStep_)};
            if ((position > lower) && (position < upper)) {
                smallest = std::min(smallest, function(position));
            }
        }
        return smallest;
    }

    PotentialKnots knots_{};
    Grid firstKnot_{};
    Grid knotStep_{};
    Grid lastKnot_{};
    Value scalePerKnotStep_{};
};

// A box of gaps: lower[r] <= g_r <= upper[r], in grid steps.
struct Box {
    GapArray lower{};
    GapArray upper{};
};

struct Statistics {
    std::uint64_t nodes{};      // boxes examined
    std::uint64_t leaves{};     // boxes accepted
    std::uint64_t basic{};      // accepted by the span test or the basic test
    std::uint64_t affine{};     // accepted by the affine test
    std::size_t maximumStack{}; // largest number of boxes waiting
};

// The cells that the distance of a pair can lie in, for a box.
struct PairRange {
    Grid first{};
    Grid last{};
};

// The branch and bound. The object owns the certificate, the table and the stack of boxes;
// nothing is allocated during run().
class BoxSearch {
  public:
    BoxSearch(const Certificate& certificate, KernelTable table)
        : certificate_{certificate}, table_{std::move(table)}, potentials_{certificate} {}

    [[nodiscard]] const Statistics& statistics() const noexcept {
        return statistics_;
    }

    // The box that could not be decided, after run() has returned Error::Unresolved.
    [[nodiscard]] const Box& lastBox() const noexcept {
        return lastBox_;
    }

    [[nodiscard]] std::expected<void, Error> run() {
        const Parameters& parameters{certificate_.parameters};
        const Value scale{parameters.scale};
        const Wide spanTarget{Wide{certificate_.rewardSumDouble + certificate_.potentialBudget} * scale};
        statistics_ = Statistics{};
        stack_[0U].lower.fill(parameters.minimumGap);
        stack_[0U].upper.fill(parameters.gridLength);
        std::size_t stackSize{1U};
        statistics_.maximumStack = 1U;
        while (stackSize > 0U) {
            --stackSize;
            Box box{stack_[stackSize]};
            ++statistics_.nodes;
            if ((statistics_.nodes % kProgressInterval) == 0U) {
                std::clog << "verify: " << statistics_.nodes << " boxes examined, " << stackSize << " waiting\n";
            }
            Grid total{0};
            for (const Grid lower : box.lower) {
                total += lower;
            }
            // 1. span test
            if ((Wide{total} * certificate_.pressure) >= spanTarget) {
                acceptBasic();
                continue;
            }
            // Beyond the span gridLength the span test holds, so the upper ends may be cut there.
            for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
                box.upper[gap] = std::min(box.upper[gap], (parameters.gridLength - total) + box.lower[gap]);
            }
            // 2. basic test
            const Value penalty{basicBound(box, total)};
            if (((2 * (base_ - (certificate_.rewardSumSimple * scale))) + penalty) >= 0) {
                acceptBasic();
                continue;
            }
            Grid width{0};
            std::size_t widest{0U};
            for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
                if ((box.upper[gap] - box.lower[gap]) > width) {
                    width = box.upper[gap] - box.lower[gap];
                    widest = gap;
                }
            }
            // 3. affine test
            if ((width <= kAffineWidth) && affineTest(box, penalty)) {
                ++statistics_.leaves;
                ++statistics_.affine;
                continue;
            }
            if (width <= 1) {
                lastBox_ = box;
                return std::unexpected(Error::Unresolved);
            }
            // 4. halve the widest interval; the lower half is examined first
            if ((stackSize + 2U) >= kStackCapacity) {
                return std::unexpected(Error::StackExhausted);
            }
            const Grid middle{(box.lower[widest] + box.upper[widest]) / 2};
            stack_[stackSize] = box;
            stack_[stackSize].lower[widest] = middle;
            ++stackSize;
            stack_[stackSize] = box;
            stack_[stackSize].upper[widest] = middle;
            ++stackSize;
            statistics_.maximumStack = std::max(statistics_.maximumStack, stackSize);
        }
        return {};
    }

  private:
    void acceptBasic() noexcept {
        ++statistics_.leaves;
        ++statistics_.basic;
    }

    // Lower bound for the left side with all points simple (stored in base_), the cells of the
    // pair distances (stored in ranges_), and the penalty of the labels (returned): twice the
    // left side minus twice the right side is at least 2 (base_ - h1 scale) + penalty for every
    // labelling. The gain of a pair with one or two double points is shared between its double
    // end points; a double point whose share is below the gain in its reward adds to the penalty.
    [[nodiscard]] Value basicBound(const Box& box, const Grid total) noexcept {
        const Parameters& parameters{certificate_.parameters};
        std::array<Value, kPointCount> share{};
        base_ = Value{total} * certificate_.pressure;
        for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
            const std::size_t first{kPairs.first[pair]};
            const std::size_t second{kPairs.second[pair]};
            Grid lower{0};
            Grid upper{0};
            for (std::size_t gap = first; gap < second; ++gap) {
                lower += box.lower[gap];
                upper += box.upper[gap];
            }
            upper = std::min(upper, (parameters.gridLength - total) + lower);
            ranges_[pair] = PairRange{.first = lower, .last = std::max(lower, upper - 1)};
            const Value kernel{table_.minimum(ranges_[pair].first, ranges_[pair].last)};
            const Value weightSimple{parameters.weights[0U][pair]};
            base_ += weightSimple * kernel;
            Value gainOneDouble{2 * (parameters.weights[1U][pair] - weightSimple) * kernel};
            Value gainTwoDouble{(parameters.weights[2U][pair] - weightSimple) * kernel};
            if (second == (first + 1U)) {
                base_ += potentials_.minimum(first, 0U, box.lower[first], box.upper[first]);
                gainOneDouble += 2 * potentials_.minimumOfDifference(first, 1U, 0U, box.lower[first], box.upper[first]);
                gainTwoDouble += potentials_.minimumOfDifference(first, 2U, 0U, box.lower[first], box.upper[first]);
            }
            const Value gain{std::min(gainOneDouble, gainTwoDouble)};
            share[first] += gain;
            share[second] += gain;
        }
        Value penalty{0};
        for (std::size_t point = 0U; point < kPointCount; ++point) {
            const Value excess{share[point] - (2 * (parameters.rewards[1U][point] - parameters.rewards[0U][point]) *
                                               parameters.scale)};
            if (excess < 0) {
                penalty += excess;
            }
        }
        return penalty;
    }

    // An affine lower bound for twice the table entry at the distance of a pair: the slope is the
    // difference of the entries next to the middle cell, and the offset makes the bound hold on
    // every cell of the range.
    void boundKernel() noexcept {
        const Grid gridLength{certificate_.parameters.gridLength};
        for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
            const PairRange range{ranges_[pair]};
            const Grid middle{(range.first + range.last) / 2};
            const Value slope{((middle <= 0) || (middle >= gridLength))
                                  ? Value{0}
                                  : table_.entry(middle + 1) - table_.entry(middle - 1)};
            Value offset{std::numeric_limits<Value>::max()};
            for (Grid cell = range.first; cell <= range.last; ++cell) {
                const Grid end{(slope >= 0) ? (cell + 1) : cell};
                offset = std::min(offset, (2 * table_.entry(cell)) - (slope * Value{end}));
            }
            kernelBounds_[pair] = AffineBound{.slope = slope, .offset = offset};
        }
    }

    // Twice the left side for one assignment of pair types, bounded below by a function that is
    // affine in the gaps and minimised over the box at a corner.
    template <typename PairType, typename GapType>
    [[nodiscard]] Wide affineValue(const Box& box, const PairType& pairType, const GapType& gapType) const noexcept {
        const Parameters& parameters{certificate_.parameters};
        std::array<Wide, kGapCount> linear{};
        Wide constant{0};
        for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
            const AffineBound& bound{potentialBounds_[gap][gapType(gap)]};
            linear[gap] = Wide{2} * (Wide{certificate_.pressure} + bound.slope);
            constant += Wide{2} * bound.offset;
        }
        for (std::size_t pair = 0U; pair < kPairCount; ++pair) {
            const Wide weight{parameters.weights[pairType(pair)][pair]};
            constant += weight * kernelBounds_[pair].offset;
            for (std::size_t gap = kPairs.first[pair]; gap < kPairs.second[pair]; ++gap) {
                linear[gap] += weight * kernelBounds_[pair].slope;
            }
        }
        Wide value{constant};
        for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
            value += linear[gap] * ((linear[gap] >= 0) ? box.lower[gap] : box.upper[gap]);
        }
        return value;
    }

    [[nodiscard]] bool affineTest(const Box& box, const Value penalty) noexcept {
        boundKernel();
        for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
            for (std::size_t type = 0U; type < kPairTypeCount; ++type) {
                potentialBounds_[gap][type] = potentials_.affineBound(gap, type, box.lower[gap], box.upper[gap]);
            }
        }
        // all points simple, with the penalty of the labels from the basic test
        const auto simple = [](const std::size_t) noexcept -> std::size_t { return 0U; };
        const Wide simpleValue{affineValue(box, simple, simple)};
        if (((simpleValue - (Wide{2} * certificate_.rewardSumSimple * certificate_.parameters.scale)) + penalty) >= 0) {
            return true;
        }
        // each labelling separately
        for (std::size_t labelling = 0U; labelling < kLabellingCount; ++labelling) {
            const std::array<std::size_t, kPairCount>& pairTypes{certificate_.pairType[labelling]};
            const std::array<std::size_t, kGapCount>& gapTypes{certificate_.gapType[labelling]};
            const Wide value{affineValue(
                box, [&pairTypes](const std::size_t pair) noexcept { return pairTypes[pair]; },
                [&gapTypes](const std::size_t gap) noexcept { return gapTypes[gap]; })};
            if (value < Wide{certificate_.rightSide[labelling]}) {
                return false;
            }
        }
        return true;
    }

    Certificate certificate_;
    KernelTable table_;
    Potentials potentials_;
    Statistics statistics_{};
    Box lastBox_{};
    Value base_{};
    std::array<PairRange, kPairCount> ranges_{};
    std::array<AffineBound, kPairCount> kernelBounds_{};
    std::array<std::array<AffineBound, kPairTypeCount>, kGapCount> potentialBounds_{};
    std::array<Box, kStackCapacity> stack_{};
};

[[nodiscard]] std::string_view describe(const Error error) noexcept {
    switch (error) {
    case Error::MalformedParameters:
        return "the parameter file is malformed";
    case Error::ParameterOutOfRange:
        return "a parameter is outside the limits of this program";
    case Error::ConditionViolated:
        return "the parameters violate a condition on local data";
    case Error::IntegerBoundExceeded:
        return "the bound for the 64-bit intermediates does not hold";
    case Error::MalformedTable:
        return "the table has the wrong size or cannot be read";
    case Error::TableEntryTooLarge:
        return "an entry of the table exceeds the scale";
    case Error::Unresolved:
        return "a box could not be decided";
    case Error::StackExhausted:
        return "the stack of boxes is full";
    }
    return "unknown error";
}

void writeStatistics(std::ostream& output, const std::string_view status, const Statistics& statistics) {
    output << R"({"status":")" << status << R"(","nodes":)" << statistics.nodes << R"(,"leaves":)" << statistics.leaves
           << R"(,"basic":)" << statistics.basic << R"(,"affine":)" << statistics.affine << R"(,"max_stack":)"
           << statistics.maximumStack << "}\n";
}

[[nodiscard]] ExitCode run(const std::span<const std::string> arguments) {
    if (arguments.size() != 3U) {
        std::cerr << "usage: verify params.txt kernel_lower.bin\n";
        return ExitCode::UsageError;
    }
    std::ifstream parameterFile{arguments[1U]};
    if (!parameterFile.is_open()) {
        std::cerr << "verify: cannot open the parameter file\n";
        return ExitCode::InputError;
    }
    const std::expected<Parameters, Error> parameters{readParameters(parameterFile)};
    if (!parameters.has_value()) {
        std::cerr << "verify: " << describe(parameters.error()) << '\n';
        return ExitCode::InputError;
    }
    const std::expected<Certificate, Error> certificate{makeCertificate(parameters.value())};
    if (!certificate.has_value()) {
        std::cerr << "verify: " << describe(certificate.error()) << '\n';
        return ExitCode::InputError;
    }
    std::ifstream tableFile{arguments[2U], std::ios::binary};
    if (!tableFile.is_open()) {
        std::cerr << "verify: cannot open the table\n";
        return ExitCode::InputError;
    }
    std::expected<KernelTable, Error> table{
        KernelTable::read(tableFile, certificate.value().parameters.gridLength, certificate.value().parameters.scale)};
    if (!table.has_value()) {
        std::cerr << "verify: " << describe(table.error()) << '\n';
        return ExitCode::InputError;
    }
    BoxSearch search{certificate.value(), std::move(table).value()};
    const std::expected<void, Error> outcome{search.run()};
    if (!outcome.has_value()) {
        std::cerr << "verify: " << describe(outcome.error()) << " (box " << search.statistics().nodes << ")\n";
        if (outcome.error() != Error::Unresolved) {
            return ExitCode::LimitError;
        }
        std::cerr << "verify: gaps of the box, in grid steps:";
        for (std::size_t gap = 0U; gap < kGapCount; ++gap) {
            std::cerr << ' ' << search.lastBox().lower[gap] << ' ' << search.lastBox().upper[gap];
        }
        std::cerr << '\n';
        writeStatistics(std::cout, "UNRESOLVED", search.statistics());
        return ExitCode::Unresolved;
    }
    writeStatistics(std::cout, "PASS_COB_CONTINUUM", search.statistics());
    return std::cout.good() ? ExitCode::Success : ExitCode::LimitError;
}

} // namespace
} // namespace certificate

int main(const int argumentCount, const char* const argumentValues[]) {
    certificate::ExitCode exitCode{certificate::ExitCode::LimitError};
    try {
        const std::span<const char* const> rawArguments{argumentValues,
                                                        static_cast<std::size_t>(std::max(argumentCount, 0))};
        std::vector<std::string> arguments{};
        arguments.reserve(rawArguments.size());
        for (const char* const argument : rawArguments) {
            arguments.emplace_back((argument != nullptr) ? argument : "");
        }
        exitCode = certificate::run(arguments);
    } catch (const std::exception& error) {
        std::cerr << "verify: " << error.what() << '\n';
    } catch (...) {
        std::cerr << "verify: unknown error\n";
    }
    return static_cast<int>(exitCode);
}
