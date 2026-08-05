#include <vector>
#include <iostream>
#include <algorithm>
#include <numeric>
#include <tuple>
#include <array>
#include <map>
#include <random>
/*
 COMPILE WITH C++17

 Andy's Afternoon Amble.

 THE TWO LANDS
   Ball.  On the truncated tetrahedron each white hexagon is surrounded by three
          black triangles alternating with the three OTHER white hexagons, so the
          hexagon adjacency graph is K4.  On the sphere V-E+F = 4-6+F = 2 gives
          four triangular faces (the black triangles): K4 with the tetrahedral
          rotation system.  Turning the same way always closes up after 3 steps.
   Floor. Deleting the black hexagons (a density 1/3 sublattice) from the tiling
          leaves every white hexagon with three white neighbours: the honeycomb
          lattice.  Turning the same way closes up after 6 steps.

 THE KEY FACT
   Andy remembers his turns, and a turn word plus a starting dart determines your
   position in any 3-regular map.  The honeycomb COVERS the tetrahedral K4 in a
   way that preserves those turns: the dart group of the honeycomb is the von
   Dyck group <r,s | r^3, s^2, (rs)^6> and the tetrahedron's is <r,s | r^3, s^2,
   (rs)^3> = A4, and (rs)^6 = ((rs)^3)^2, so r -> r, s -> s is a surjection.  Its
   kernel is the deck group (translations by 2*Lambda together with half-turns
   about hexagon centres), whose four orbits of tiles are the four fibres.  A
   hexagonal face is fixed by the half-turn about its own centre, so it wraps
   twice around a triangle downstairs -- confirming the quotient is the SPHERE's
   K4 and not, say, K4 on a torus.

   So Andy's imagined position on the ball is just the FIBRE of the tile he is
   really standing on, and since real-home implies home-fibre he is never told
   "not home" while at home.  He learns the truth exactly when the ball says
   "home" too early:

        p = 1 - P(the first return to the home fibre lands on the home tile).

 THE COLLAPSE TO A HEXAGON
   Every tile off the home fibre has exactly ONE neighbour on it (its three
   neighbours carry the three other fibres).  Hence the floor minus the home
   fibre is 2-regular: a disjoint union of cycles, and they turn out to be single
   hexagonal rings.  Andy's first step drops him on one such ring, and exactly
   one tile of that ring -- the one he is standing on -- leaks back to home.  The
   whole infinite lattice problem is therefore a random walk on a 6-cycle that
   leaks with probability 1/3 at each tile:

        f0 = 1/3 + (2/3) f1,  f1 = (f0+f2)/3,  f2 = (f1+f3)/3,  f3 = (2/3) f2
        =>  f0 = 9/20   =>   p = 11/20.

 This program derives all of that from the geometry and solves it in exact
 rational arithmetic, then checks the answer with a coupled simulation that runs
 one shared stream of turns on a real truncated tetrahedron and on the floor.
*/

namespace
{
    const int VERIFY_STEPS = 16;
    const int MONTE_CARLO_TRIALS = 2000000;
    const unsigned int RANDOM_SEED = 20260804;

    // A white floor tile.  (m, n, t) sits at m*(sqrt3,0) + n*(sqrt3/2,3/2) + t*(0,1).
    using Tile = std::tuple<int, int, int>;
    const Tile HOME{ 0, 0, 0 };

    // Which of the ball's four hexagons a floor tile corresponds to: the four
    // orbits of the deck group of the covering honeycomb -> K4.
    using Fibre = std::pair<int, int>;

    // The ball's four white hexagons, each adjacent to the other three, listed
    // counterclockwise as seen from outside.  This is the spherical (tetrahedral)
    // rotation system -- VerifyFaces() checks that its faces are triangles.
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

// Walk around a face by always taking the next neighbour in the cyclic order.
// Three steps on the ball (triangles), six on the floor (hexagons).
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

// Every tile's three neighbours must carry the three OTHER fibres.  That is the
// covering property, and it is what forces the floor-minus-home-fibre to be a
// disjoint union of cycles.
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

// Exact law of the first time Andy stands on a home-fibre tile.  If the covering
// is right this must equal the K4 first-return law (2/3)^(k-2)/3.
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

// The cycle of non-home-fibre tiles that Andy's first step lands him on.
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

// The unique home-fibre neighbour that each ring tile leaks into.
std::vector<Tile> LeakTargets(const std::vector<Tile>& ring)
{
    std::vector<Tile> targets;
    for (const Tile& tile : ring)
        for (const Tile& w : Neighbours(tile))
            if (OnHomeFibre(w)) { targets.push_back(w); break; }
    return targets;
}

// Random walk on the ring: at each tile 1/3 to leak off it, 1/3 each way around.
// f[i] = P(the leak happens into the HOME tile | standing on ring tile i).
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

// Independent check: drive a walk on the real truncated tetrahedron and a walk on
// the floor with ONE shared stream of turns, and see which reaches home first.
double CoupledMonteCarlo(int trials, int& coveringViolations)
{
    std::mt19937 rng(RANDOM_SEED);
    std::uniform_int_distribution<int> turn(0, 2);
    int detected{ 0 };
    coveringViolations = 0;
    for (int t{ 0 }; t < trials; ++t)
    {
        const int first = turn(rng);                        // the first step records no turn
        int ballPrevious{ BALL_HOME }, ballCurrent{ BALL[BALL_HOME][first] };
        Tile floorPrevious{ HOME }, floorCurrent{ Neighbours(HOME)[first] };
        while (true)
        {
            const int choice = turn(rng);                   // 0 = back, 1 and 2 = the two turns
            const int ballNext = BALL[ballCurrent][(IndexOf(BALL[ballCurrent], ballPrevious) + choice) % 3];
            const auto around = Neighbours(floorCurrent);
            const Tile floorNext = around[(IndexOf(around, floorPrevious) + choice) % 3];
            ballPrevious = ballCurrent; ballCurrent = ballNext;
            floorPrevious = floorCurrent; floorCurrent = floorNext;

            if (floorCurrent == HOME && ballCurrent != BALL_HOME) { ++coveringViolations; break; }
            if (ballCurrent == BALL_HOME)
            {
                if (!(floorCurrent == HOME)) ++detected;     // the ball says home, Andy is not
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
