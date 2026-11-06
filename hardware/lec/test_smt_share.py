#!/usr/bin/env python3
"""Narrow semantic regressions for the solver-boundary sharing transformation."""
import os
import subprocess
import unittest

from smt_share import find_smtio, shared_query


class SharingTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.smtio = find_smtio(os.environ.get('YOSYS_BIN', 'yosys'), os.environ.get('YOSYS_SMTIO'))

    def solve(self, query):
        result = subprocess.run([os.environ.get('Z3_BIN', 'z3'), '-T:5', '-in'],
                                input=query, text=True, capture_output=True, check=True)
        self.assertNotIn('(error', result.stdout)
        return result.stdout

    def test_equivalence_and_actual_fault_preserve_model_names(self):
        # Two named state applications and a next-state equation exercise the
        # production unroller's registered-circuit path as well as output terms.
        base = '''(declare-sort |m_s| 0)
(declare-fun |m#0| (|m_s|) (_ BitVec 8))
(define-fun |m_n x| ((state |m_s|)) (_ BitVec 8) (|m#0| state))
(declare-const s |m_s|)
(declare-const s1 |m_s|)
(declare-const model_only |m_s|)
(define-fun in_0 () (_ BitVec 8) (|m_n x| s))
(define-fun next_0 () (_ BitVec 8) (|m_n x| s1))
(assert (= next_0 (bvadd in_0 #x01)))
(define-fun |spec_out| () (_ BitVec 8) (bvadd in_0 #x01))
'''
        for fault, expected in ((False, 'unsat'), (True, 'sat')):
            rtl = '(bvxor next_0 #x01)' if fault else 'next_0'
            query = base + f'(define-fun |rtl_out| () (_ BitVec 8) {rtl})\n(assert (not (= |rtl_out| |spec_out|)))\n(check-sat)\n'
            if fault:
                query += '(get-value (|rtl_out| |spec_out| (|m_n x| model_only)))\n'
            transformed = shared_query(query, self.smtio)
            self.assertEqual(self.solve(query).splitlines()[0], expected)
            result = self.solve(transformed)
            self.assertEqual(result.splitlines()[0], expected)
            if fault:
                self.assertIn('rtl_out', result)
                self.assertIn('spec_out', result)

    def test_bitvector_uf_congruence_and_mismatch(self):
        base = '''(declare-fun product ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(define-fun lhs () (_ BitVec 8) (product x #x01))
'''
        for rhs, expected in (('(product x #x01)', 'unsat'), ('(product x #x02)', 'sat')):
            query = base + f'(assert (not (= lhs {rhs})))\n(check-sat)\n'
            self.assertEqual(self.solve(shared_query(query, self.smtio)).strip(), expected)

    def test_refuse_scope_reset_and_conflicting_definitions(self):
        for query in ('(push 1)\n(check-sat)', '(pop 1)\n(check-sat)',
                      '(reset)\n(check-sat)', '(reset-assertions)\n(check-sat)',
                      '(set-option :global-decls true)\n(check-sat)',
                      '(check-sat)\n(assert false)',
                      '(check-sat)\n(check-sat)',
                      '(declare-fun x () Bool)\n(define-fun x () Bool true)\n(check-sat)'):
            with self.subTest(query=query), self.assertRaises((ValueError, AssertionError)):
                shared_query(query, self.smtio)


if __name__ == '__main__':
    unittest.main()
