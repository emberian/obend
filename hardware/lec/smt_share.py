#!/usr/bin/env python3
"""Keep LEC expressions shared without changing their SMT meaning.

Yosys's own smtio.py unrolls state-function applications; fresh constants plus
all their defining equalities then replace zero-argument macros. This exact
definitional extension prevents exponential parser expansion before check-sat.
No output obligation, input constraint or counterexample request is removed.

Referent: Yosys 0.33 backends/smt2/smtio.py, SmtIo.unroll_stmt/write:
https://github.com/YosysHQ/yosys/blob/yosys-0.33/backends/smt2/smtio.py
The installed Yosys implementation is used, never copied or reimplemented.
"""
import argparse
from dataclasses import dataclass
import importlib.util
import io
import os
from pathlib import Path
import shutil
import sys


@dataclass
class Command:
    start: int
    end: int
    form: object


def commands(text):
    """Read S-expressions, retaining spans; comments/quoted symbols are lexical."""
    tokens = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
            continue
        if text[i] == ';':
            end = text.find('\n', i)
            i = len(text) if end == -1 else end + 1
            continue
        start = i
        if text[i] in '()':
            i += 1
        elif text[i] == '|':
            end = text.find('|', i + 1)
            if end == -1:
                raise ValueError('unterminated quoted symbol')
            i = end + 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '"':
                    i += 1
                    if i < len(text) and text[i] == '"':
                        i += 1
                        continue
                    break
                i += 1
            else:
                raise ValueError('unterminated string')
        else:
            while i < len(text) and not text[i].isspace() and text[i] not in '();':
                i += 1
        tokens.append((text[start:i], start, i))

    pos = 0

    def read():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError('unfinished S-expression')
        token, start, end = tokens[pos]
        pos += 1
        if token == ')':
            raise ValueError('unexpected closing parenthesis')
        if token != '(':
            return token, start, end
        items = []
        while pos < len(tokens) and tokens[pos][0] != ')':
            item, _, _ = read()
            items.append(item)
        if pos >= len(tokens):
            raise ValueError('unfinished S-expression')
        end = tokens[pos][2]
        pos += 1
        return items, start, end

    result = []
    while pos < len(tokens):
        form, start, end = read()
        if not isinstance(form, list) or not form or not isinstance(form[0], str):
            raise ValueError('top-level command must be a nonempty S-expression')
        result.append(Command(start, end, form))
    return result


def symbol(atom):
    return atom[1:-1] if atom.startswith('|') and atom.endswith('|') else atom


def render(form):
    return '(' + ' '.join(map(render, form)) + ')' if isinstance(form, list) else form


def data_sort(sort):
    return sort == 'Bool' or (isinstance(sort, list) and len(sort) == 3
                              and sort[:2] == ['_', 'BitVec'])


def data_declaration(form):
    return form[0] == 'declare-fun' and len(form) == 4 and data_sort(form[3]) and all(
        data_sort(sort) for sort in form[2]
    )


def shared_query(text, smtio_path, keep_defines=False):
    """Yosys's production unroller, followed by exact ground definitions.

    smtio.py::SmtIo.unroll_stmt memoizes applications to the named states and
    supports the generated single-query LEC input. Dummy mode performs only
    that transformation: it never starts or stops a solver process. SMT-LIB's
    declare-const shorthand is expanded because smtio expects declare-fun.

    Every resulting `define-fun f () S body` becomes a fresh constant of sort S
    plus `(assert (= f body))` (or stays a ground `define-fun` when
    `keep_defines=True` for DAG-hash-consing solvers such as Bitwuzla). This
    exact definitional extension retains every equation while avoiding
    exponential macro expansion in the SMT parser.
    """
    source = commands(text)
    checks = [i for i, c in enumerate(source) if c.form == ['check-sat']]
    if len(checks) != 1 or any(c.form[0] != 'get-value' for c in source[checks[0] + 1:]):
        raise ValueError('expected one check-sat followed only by get-value commands')
    if any(c.form[0] == 'get-value' for c in source[:checks[0]]):
        raise ValueError('get-value must follow check-sat')
    spec = importlib.util.spec_from_file_location('lec_yosys_smtio', smtio_path)
    if spec is None or spec.loader is None:
        raise ValueError('cannot load Yosys smtio.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    opts = module.SmtOpts()
    opts.solver = 'dummy'
    opts.dummy_file = os.devnull
    opts.unroll = True
    # State unrolling normally removes all UFs. Keep the logic's UF capability
    # when the original multiplication abstraction declares data-only functions.
    has_uf = any(data_declaration(c.form) and c.form[2] for c in source)
    if has_uf:
        opts.logic = 'QF_AUFBV'
    opts.debug_file = io.StringIO()
    solver = module.SmtIo(opts)
    try:
        for c in source:
            f = c.form
            # Replacing definitions with assertions requires identical lifetimes.
            # LEC emits one global query; refuse scope/reset modes rather than
            # silently changing declaration-versus-assertion persistence.
            if f[0] in {'push', 'pop', 'reset', 'reset-assertions'} or (
                f[0] == 'set-option' and len(f) > 1 and f[1] == ':global-decls'
            ):
                raise ValueError('scope/reset controls are outside single-query LEC')
            if f[0] == 'declare-const':
                if len(f) != 3:
                    raise ValueError('malformed declare-const')
                f = ['declare-fun', f[1], [], f[2]]
            # Yosys 0.33's state-unroll declaration scan assumes atomic sorts.
            # Declarations over Bool/bit-vectors contain no state objects and
            # need no unrolling; retain them, including the existing multiply UF.
            solver.write(solver.unparse(f), unroll=not data_declaration(f))
        unrolled = opts.debug_file.getvalue()
    finally:
        if hasattr(solver, 'dummy_fd'):
            solver.dummy_fd.close()
        opts.debug_file.close()
    result = []
    queries = []
    declared = set()
    for c in commands(unrolled):
        f = c.form
        if f[0] in {'check-sat', 'get-value'}:
            if f == ['check-sat'] and has_uf and not keep_defines:
                queries.append('(check-sat-using (then simplify propagate-values solve-eqs smt))')
            else:
                queries.append(unrolled[c.start:c.end])
            continue
        if f[0] in {'declare-fun', 'define-fun'}:
            name = symbol(f[1])
            if name in declared:
                raise ValueError(f'conflicting declaration: {name}')
            declared.add(name)
        if f[0] == 'define-fun':
            if len(f) != 5 or f[2] != []:
                raise ValueError('unroller left a nonground function definition')
            if keep_defines:
                result.append(unrolled[c.start:c.end])
            else:
                result.append(render(['declare-fun', f[1], [], f[3]]))
                result.append(render(['assert', ['=', f[1], f[4]]]))
        else:
            result.append(unrolled[c.start:c.end])
    # Model-only state getters can be unrolled lazily while reading get-value.
    # Their fresh total definitions must precede check-sat: an assertion after
    # solving invalidates Z3's model. Source validation above ensures no original
    # post-check constraint is moved. Keep original get-value requests last.
    return '\n'.join(result + queries) + '\n'


def find_smtio(yosys, override=None):
    if override:
        path = Path(override)
        if not path.is_file():
            raise ValueError(f'YOSYS_SMTIO does not name a file: {path}')
        return path
    binary = Path(shutil.which(yosys) or yosys).resolve()
    datadir = binary.parent.parent / 'share' / 'yosys'
    for path in (datadir / 'smtio.py', datadir / 'python3' / 'smtio.py'):
        if path.is_file():
            return path
    raise ValueError(f'cannot locate smtio.py beside {binary}; set YOSYS_SMTIO')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--yosys', required=True)
    parser.add_argument('--smtio', default=os.environ.get('YOSYS_SMTIO'))
    parser.add_argument('--keep-defines', action='store_true')
    args = parser.parse_args()
    try:
        path = find_smtio(args.yosys, args.smtio)
        args.output.write_text(shared_query(args.input.read_text(), path, keep_defines=args.keep_defines))
        return 0
    except (ValueError, OSError, AssertionError, ImportError) as error:
        print(f'[FAIL] SMT sharing: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
