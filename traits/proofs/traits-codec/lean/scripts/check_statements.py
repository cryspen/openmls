#!/usr/bin/env python3
"""Check that every theorem of TraitsCodec/Verification/ProofObligations.lean (and the
names of AxiomCheck.lean) has exactly the statement generated in
TraitsCodec/Extraction/ProofObligations.lean (whitespace-insensitive), and that no
generated obligation is missing. Usage: python3 scripts/check_statements.py"""
import re, sys, os
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
def stmts(path):
    s = open(path).read()
    d = {}
    for m in re.finditer(r'^theorem\s+(.*?):=', s, re.M | re.S):
        t = ' '.join(m.group(1).split())
        name, _, stmt = t.partition(' ')  # statement = binders + type
        d[name] = stmt
    return d
g = stmts('TraitsCodec/Extraction/ProofObligations.lean')
v = stmts('TraitsCodec/Verification/ProofObligations.lean')
bad = 0
for n, st in g.items():
    if n not in v: print('MISSING', n); bad += 1
    elif v[n] != st: print('DIFFERENT', n); bad += 1
for n in v:
    if n not in g: print('EXTRA', n); bad += 1
ax = open('TraitsCodec/Verification/AxiomCheck.lean').read()
axn = set(re.findall(r'#print axioms (\S+)', ax))
for n in g:
    if n not in axn: print('NOT IN AxiomCheck', n); bad += 1
print(f'{len(g)} generated, {len(v)} in Verification, {bad} problem(s)')
sys.exit(1 if bad else 0)
