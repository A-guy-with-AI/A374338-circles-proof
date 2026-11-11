"""Simulation cartésienne de cercles unité, sans hypothèse de réseau."""

import argparse
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path


Point = tuple[float, float]


class SpatialIndex:
    """Index de points en cases cartésiennes, sans modification des coordonnées."""

    def __init__(self, width: float):
        self.width = width
        self.bins = defaultdict(list)
        self.points: list[Point] = []

    def cell(self, point: Point) -> tuple[int, int]:
        x, y = point
        return math.floor(x / self.width), math.floor(y / self.width)

    def nearby(self, point: Point, radius: float):
        x, y = self.cell(point)
        reach = math.ceil(radius / self.width)
        for i in range(x - reach, x + reach + 1):
            for j in range(y - reach, y + reach + 1):
                yield from self.bins.get((i, j), ())

    def append(self, point: Point) -> int:
        index = len(self.points)
        self.points.append(point)
        self.bins[self.cell(point)].append(index)
        return index


def intersections(a: Point, b: Point, tolerance: float, tangencies: bool):
    """Milieu de la corde commune, puis déplacement normal à la ligne des centres."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    distance = math.hypot(dx, dy)
    if distance > 2 + tolerance:
        return ()
    assert distance > tolerance
    mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
    if distance >= 2 - tolerance:
        return ((mx, my),) if tangencies else ()
    scale = math.sqrt(1 - (distance / 2)**2) / distance
    return (mx - scale * dy, my + scale * dx), (mx + scale * dy, my - scale * dx)


def simulate(seeds: list[Point], rounds: int, tolerance: float, tangencies: bool):
    vertices = SpatialIndex(tolerance)
    centers = SpatialIndex(2)

    def vertex_id(point: Point) -> int:
        for index in vertices.nearby(point, tolerance):
            if math.dist(point, vertices.points[index]) <= tolerance:
                return index
        return vertices.append(point)

    for seed in seeds:
        vertex_id(seed)
    next_center = 0
    for n in range(1, rounds + 1):
        last_center = len(vertices.points)
        for center in vertices.points[next_center:last_center]:
            joined = False
            for old in centers.nearby(center, 2 + tolerance):
                hits = intersections(center, centers.points[old], tolerance, tangencies)
                if hits:
                    joined = True
                for point in hits:
                    vertex_id(point)
            # Dans les deux expériences, chaque cercle rejoint l'union connexe.
            assert not centers.points or joined, (n, center)
            centers.append(center)
        next_center = last_center

        # Même sans créer de sommet par tangence, un sommet présent
        # découpe tous les cercles qui le portent.
        incidences = [0] * len(centers.points)
        for point in vertices.points:
            for index in centers.nearby(point, 1 + tolerance):
                if abs(math.dist(point, centers.points[index]) - 1) <= tolerance:
                    incidences[index] += 1
        assert all(count >= 2 for count in incidences)
        edges = sum(incidences)
        count = len(vertices.points)
        yield count, edges, edges - count + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--iterations', type=int, default=52)
    parser.add_argument('--tolerance', type=float, default=1e-8)
    parser.add_argument('--sans-tangences', action='store_true')
    parser.add_argument('--references', type=Path)
    args = parser.parse_args()
    if args.iterations < 1:
        parser.error('il faut au moins une itération')
    if not 0 < args.tolerance < 0.01:
        parser.error('la tolérance doit être dans ]0, 0.01[')
    tangencies = not args.sans_tangences
    columns = ['n', 'A374338', 'A374339', 'A374337', 'A400701']
    two = simulate([(0., 0.), (1., 0.)], args.iterations, args.tolerance, tangencies)
    five = simulate([(float(x), 0.) for x in range(5)], args.iterations, args.tolerance, tangencies)
    rows = {
        n: dict(zip(columns[1:], (*first, second[0])))
        for n, (first, second) in enumerate(zip(two, five), 1)
    }
    if args.references:
        compared = defaultdict(int)
        with args.references.open() as handle:
            for series, index, term in csv.reader(handle):
                n, expected = int(index), int(term)
                if n in rows:
                    actual = rows[n][series]
                    if actual != expected:
                        raise SystemExit(f'{series}({n}): calculé {actual}, publié {expected}')
                    compared[series] += 1
        for series, count in sorted(compared.items()):
            print(f'{series}: {count} termes concordants', file=sys.stderr)
    writer = csv.DictWriter(sys.stdout, columns, lineterminator='\n')
    writer.writeheader()
    for n, row in rows.items():
        writer.writerow(dict(n=n, **row))


if __name__ == '__main__':
    main()
