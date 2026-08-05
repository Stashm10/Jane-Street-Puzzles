#include <vector>
#include <iostream>
#include <algorithm>
#include <numeric>
#include <tuple>
#include <array>
#include <map>
#include <random>

namespace
{
    const int VERIFY_STEPS = 16;
    const int MONTE_CARLO_TRIALS = 2000000;
    const unsigned int RANDOM_SEED = 20260804;

    using Tile = std::tuple<int, int, int>;
    const Tile HOME{ 0, 0, 0 };

   
    using Fibre = std::pair<int, int>;


    const std::array<std::array<int, 3>, 4> BALL{ { {1,2,3}, {0,3,2}, {0,1,3}, {0,2,1} } };
    const int BALL_HOME = 0;
}

struct Fraction
{
    long long num{ 0 }, den{ 1 };

    Fraction() = default;
    Fraction(long long n, long long d = 1) : num{ n }, den{ d } { Reduce(); }

    void Reduce()
    {
        if (den < 0) { num = -num; den = -den; }
        const long long g = std::gcd(num < 0 ? -num : num, den);
        if (g > 1) { num /= g; den /= g; }
        if (0 == num) den = 1;
    }

    Fraction operator+(const Fraction& o) const { return Fraction(num * o.den + o.num * den, den * o.den); }
    Fraction operator-(const Fraction& o) const { return Fraction(num * o.den - o.num * den, den * o.den); }
    Fraction operator*(const Fraction& o) const { return Fraction(num * o.num, den * o.den); }
    Fraction operator/(const Fraction& o) const { return Fraction(num * o.den, den * o.num); }
    bool operator==(const Fraction& o) const { return num == o.num && den == o.den; }
    bool operator!=(const Fraction& o) const { return !(*this == o); }
    explicit operator double() const { return static_cast<double>(num) / static_cast<double>(den); }
};

std::ostream& operator<<(std::ostream& out, const Fraction& f)
{
    return out << f.num << '/' << f.den;
}

template <class C, class T>
int IndexOf(const C& container, const T& value)
{
    return static_cast<int>(std::find(container.begin(), container.end(), value) - container.begin());
}

// The three white neighbours of a floor tile, counterclockwise (Andy walks on
// top of the floor and on the outside of the ball, so the handedness matches).
std::array<Tile, 3> Neighbours(const Tile& tile)
{
    const auto [m, n, t] = tile;
    if (0 == t)     // pointing at  90, 210, 330 degrees
        return { Tile{ m, n, 1 }, Tile{ m, n - 1, 1 }, Tile{ m + 1, n - 1, 1 } };
    return { Tile{ m, n + 1, 0 }, Tile{ m - 1, n + 1, 0 }, Tile{ m, n, 0 } };  // 30, 150, 270
}

Fibre WhichHexagon(const Tile& tile)
{
    const auto [m, n, t] = tile;
    return { ((m + t) % 2 + 2) % 2, ((n % 2) + 2) % 2 };
}

bool OnHomeFibre(const Tile& tile) { return WhichHexagon(tile) == WhichHexagon(HOME); }


int BallFaceLength()
{
    const int startFrom{ 0 }, startTo{ BALL[0][0] };
    int from{ startFrom }, to{ startTo }, length{ 0 };
    do
    {
        const int nxt = BALL[to][(IndexOf(BALL[to], from) + 1) % 3];
        from = to; to = nxt;
        ++length;
    } while (!(from == startFrom && to == startTo) && length < 64);
    return length;
}

int FloorFaceLength()
{
    const Tile startFrom{ HOME }, startTo{ Neighbours(HOME)[0] };
    Tile from{ startFrom }, to{ startTo };
    int length{ 0 };
    do
    {
        const auto ring = Neighbours(to);
        const Tile nxt = ring[(IndexOf(ring, from) + 1) % 3];
        from = to; to = nxt;
        ++length;
    } while (!(from == startFrom && to == startTo) && length < 64);
    return length;
}


bool VerifyCoveringProperty(int radius)
{
    for (int m{ -radius }; m <= radius; ++m)
        for (int n{ -radius }; n <= radius; ++n)
            for (int t{ 0 }; t < 2; ++t)
            {
                const Tile tile{ m, n, t };
                std::vector<Fibre> seen;
                for (const Tile& w : Neighbours(tile))
                    seen.push_back(WhichHexagon(w));
                std::sort(seen.begin(), seen.end());
                if (std::unique(seen.begin(), seen.end()) != seen.end()) return false;
                if (std::find(seen.begin(), seen.end(), WhichHexagon(tile)) != seen.end()) return false;
            }
    return true;
}

std::vector<Fraction> FibreHitLaw(int steps)
{
    std::map<std::pair<Tile, Tile>, Fraction> alive{ { { HOME, HOME }, Fraction{ 1 } } };
    std::vector<Fraction> law(steps + 1);
    for (int step{ 1 }; step <= steps; ++step)
    {
        std::map<std::pair<Tile, Tile>, Fraction> next;
        for (const auto& [state, probability] : alive)
        {
            const Tile& current = state.second;
            for (const Tile& w : Neighbours(current))
            {
                const Fraction share = probability * Fraction{ 1, 3 };
                if (OnHomeFibre(w))
                    law[step] = law[step] + share;
                else
                {
                    const std::pair<Tile, Tile> key{ current, w };
                    next[key] = next[key] + share;
                }
            }
        }
        alive = next;
    }
    return law;
}


std::vector<Tile> HomeRing()
{
    const Tile start = Neighbours(HOME)[0];
    std::vector<Tile> ring{ start };
    Tile previous{ HOME }, current{ start };
    while (true)
    {
        Tile next{ current };
        for (const Tile& w : Neighbours(current))
            if (!OnHomeFibre(w) && !(w == previous)) { next = w; break; }
        previous = current;
        current = next;
        if (current == start) break;
        ring.push_back(current);
        if (ring.size() > 64) break;
    }
    return ring;
}


std::vector<Tile> LeakTargets(const std::vector<Tile>& ring)
{
    std::vector<Tile> targets;
    for (const Tile& tile : ring)
        for (const Tile& w : Neighbours(tile))
            if (OnHomeFibre(w)) { targets.push_back(w); break; }
    return targets;
}


std::vector<Fraction> SolveRing(const std::vector<Tile>& ring, const std::vector<Tile>& leaks)
{
    const int size = static_cast<int>(ring.size());
    std::vector<std::vector<Fraction>> matrix(size, std::vector<Fraction>(size + 1));
    for (int i{ 0 }; i < size; ++i)
    {
        matrix[i][i] = matrix[i][i] + Fraction{ 1 };
        matrix[i][(i + 1) % size] = matrix[i][(i + 1) % size] - Fraction{ 1, 3 };
        matrix[i][(i - 1 + size) % size] = matrix[i][(i - 1 + size) % size] - Fraction{ 1, 3 };
        matrix[i][size] = (leaks[i] == HOME) ? Fraction{ 1, 3 } : Fraction{ 0 };
    }
    for (int column{ 0 }; column < size; ++column)
    {
        int pivot{ column };
        while (pivot < size && matrix[pivot][column] == Fraction{ 0 }) ++pivot;
        std::swap(matrix[column], matrix[pivot]);
        const Fraction scale = matrix[column][column];
        for (Fraction& entry : matrix[column]) entry = entry / scale;
        for (int row{ 0 }; row < size; ++row)
        {
            if (row == column || matrix[row][column] == Fraction{ 0 }) continue;
            const Fraction factor = matrix[row][column];
            for (int c{ 0 }; c <= size; ++c)
                matrix[row][c] = matrix[row][c] - factor * matrix[column][c];
        }
    }
    std::vector<Fraction> f;
    for (int i{ 0 }; i < size; ++i) f.push_back(matrix[i][size]);
    return f;
}


double CoupledMonteCarlo(int trials, int& coveringViolations)
{
    std::mt19937 rng(RANDOM_SEED);
    std::uniform_int_distribution<int> turn(0, 2);
    int detected{ 0 };
    coveringViolations = 0;
    for (int t{ 0 }; t < trials; ++t)
    {
        const int first = turn(rng);                        
        int ballPrevious{ BALL_HOME }, ballCurrent{ BALL[BALL_HOME][first] };
        Tile floorPrevious{ HOME }, floorCurrent{ Neighbours(HOME)[first] };
        while (true)
        {
            const int choice = turn(rng);                   
            const int ballNext = BALL[ballCurrent][(IndexOf(BALL[ballCurrent], ballPrevious) + choice) % 3];
            const auto around = Neighbours(floorCurrent);
            const Tile floorNext = around[(IndexOf(around, floorPrevious) + choice) % 3];
            ballPrevious = ballCurrent; ballCurrent = ballNext;
            floorPrevious = floorCurrent; floorCurrent = floorNext;

            if (floorCurrent == HOME && ballCurrent != BALL_HOME) { ++coveringViolations; break; }
            if (ballCurrent == BALL_HOME)
            {
                if (!(floorCurrent == HOME)) ++detected;     
                break;
            }
        }
    }
    return static_cast<double>(detected) / trials;
}

Fraction Solution()
{
    std::cout << "Ball : consistent-turn face length = " << BallFaceLength()
              << "  (3 => triangular faces => the sphere's K4)" << std::endl;
    std::cout << "Floor: consistent-turn face length = " << FloorFaceLength()
              << "  (6 => hexagonal faces)" << std::endl;
    std::cout << "Covering property (every tile sees the three other hexagons): "
              << (VerifyCoveringProperty(8) ? "holds" : "FAILS") << std::endl;

    const std::vector<Fraction> law = FibreHitLaw(VERIFY_STEPS);
    bool matches{ true };
    Fraction k4{ 1, 3 };
    for (int k{ 2 }; k <= VERIFY_STEPS; ++k)
    {
        if (law[k] != k4) matches = false;
        k4 = k4 * Fraction{ 2, 3 };
    }
    std::cout << "First home-fibre hit vs the K4 first-return law (2/3)^(k-2)/3 up to k="
              << VERIFY_STEPS << ": " << (matches ? "identical" : "MISMATCH") << std::endl;
    std::cout << "    P(T=2) = " << law[2] << "   P(T=3) = " << law[3]
              << "   P(T=4) = " << law[4] << std::endl;

    const std::vector<Tile> ring = HomeRing();
    const std::vector<Tile> leaks = LeakTargets(ring);
    std::cout << "Andy's first step lands on a ring of " << ring.size()
              << " tiles; leaks-to-home pattern: ";
    for (const Tile& target : leaks) std::cout << (target == HOME ? 'H' : '.');
    std::cout << std::endl;

    const std::vector<Fraction> f = SolveRing(ring, leaks);
    std::cout << "Exact solve of the ring walk, f =";
    for (const Fraction& value : f) std::cout << ' ' << value;
    std::cout << std::endl;

    const Fraction fooled = f[0];
    const Fraction p = Fraction{ 1 } - fooled;
    std::cout << "P(amble ends at home, Andy none the wiser) = " << fooled
              << " = " << static_cast<double>(fooled) << std::endl;

    int violations{ 0 };
    const double simulated = CoupledMonteCarlo(MONTE_CARLO_TRIALS, violations);
    std::cout << "Coupled simulation over " << MONTE_CARLO_TRIALS << " ambles: p ~ "
              << simulated << "   (covering violations: " << violations << ')' << std::endl;

    return p;
}

int main()
{
    const Fraction solution = Solution();
    std::cout << std::endl;
    std::cout << "Answer: " << solution << " = " << static_cast<double>(solution) << std::endl;
    return 0;
}
