"""Replay reserve-coordinate exclusions and the old selected-sign distance bound."""

from argparse import ArgumentParser
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from r_paley_gamma_quadratic import CHOSEN, RESERVE, source_data
from r_paley_lattice_lift import signs


def input_data():
    _, units, positions, selected, x_rows, v_rows = source_data()
    lines = [' '.join(map(str, positions[:15]))]
    for matrix in (units, selected):
        lines.extend(' '.join(map(str, row)) for row in matrix)
    for x_row, v_row in zip(x_rows, v_rows, strict=True):
        lines.append(' '.join(map(str, (*signs(x_row, CHOSEN), *signs(v_row, RESERVE)))))
    return '\n'.join(lines) + '\n'


def verify(section):
    source = Path(__file__).with_suffix('.cpp')
    data = input_data()
    with TemporaryDirectory() as directory:
        binary = Path(directory) / 'gamma_coordinate_radius'
        run(['g++', '-O3', '-std=c++20', str(source), '-o', str(binary)], check=True)
        run([str(binary), section], input=data, text=True, check=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--section', choices=('all', 'reserve', 'selected'), default='all')
    verify(parser.parse_args().section)
