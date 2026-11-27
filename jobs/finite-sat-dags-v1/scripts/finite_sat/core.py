"""Small transparent DIMACS builders; no solver or mathematical pruning."""
import hashlib
import shutil
from pathlib import Path


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


class MemoryCNF:
    def __init__(self):
        self.variables = {}
        self.clauses = []

    @property
    def nvars(self):
        return len(self.variables)

    @property
    def nclauses(self):
        return len(self.clauses)

    def var(self, key):
        key = tuple(key)
        if key not in self.variables:
            self.variables[key] = len(self.variables) + 1
        return self.variables[key]

    def add(self, clause):
        clause = tuple(clause)
        if any(type(x) is not int or not 0 < abs(x) <= self.nvars for x in clause):
            raise ValueError('undeclared variable or invalid literal')
        self.clauses.append(clause)

    def satisfied(self, model):
        values = set(model)
        if any(-x in values for x in values):
            return False
        return all(any(x in values for x in c) for c in self.clauses)

    def write(self, path, extra=()):
        extra = [tuple(c) for c in extra]
        with Path(path).open('w') as out:
            out.write(f'p cnf {self.nvars} {self.nclauses + len(extra)}\n')
            for c in self.clauses + extra:
                out.write(' '.join(map(str, c)) + (' ' if c else '') + '0\n')
        return sha256(path)


class StreamCNF:
    """Stream clauses, then prepend the exact header; IDs remain deterministic."""
    def __init__(self, path):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.body_path = self.path.with_suffix(self.path.suffix + '.body')
        self.body = self.body_path.open('w')
        self.variables = {}
        self.nclauses = 0

    @property
    def nvars(self):
        return len(self.variables)

    def var(self, key):
        key = tuple(key)
        if key not in self.variables:
            self.variables[key] = len(self.variables) + 1
        return self.variables[key]

    def add(self, clause):
        clause = tuple(clause)
        if any(type(x) is not int or not 0 < abs(x) <= self.nvars for x in clause):
            raise ValueError('undeclared variable or invalid literal')
        self.body.write(' '.join(map(str, clause)) + (' ' if clause else '') + '0\n')
        self.nclauses += 1

    def finish(self):
        self.body.close()
        with self.path.open('w') as out, self.body_path.open() as body:
            out.write(f'p cnf {self.nvars} {self.nclauses}\n')
            shutil.copyfileobj(body, out)
        self.body_path.unlink()
        return sha256(self.path)
