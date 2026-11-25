"""Slice the exact input of the four private declarations while preserving their names and context."""
import hashlib


MODULE = 'Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsAtStart'
BLOB = 'e3a5718510d9f02ffd379d894b692c600307aa9b'
PATH = 'src/'+MODULE.replace('.','/')+'.lean'
NAMES = ('placeMapL_eq','vecAtL_eq','setupVecAtL_eq','gens_eq_pz')


def variants(data):
    digest = hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()
    if digest != BLOB:
        raise ValueError('source differs from verified B13 RowsAtStart')
    lines = data.decode().splitlines(keepends=True)
    assert lines[62].startswith('import Lean.Exception') and lines[705]=='section -- clump:auto\n'
    assert 'local elab "exact_by_kernel "' in lines[723]
    prefix=''.join([*lines[:63], *(['\n']*(705-63)), *lines[705:738]])
    # Auto-generated module sections plus the source's explicit public, noncomputable, and namespace scopes.
    suffix='end GlobalTheory.HeightCounting.Fin3\nend\nend\nend -- clump:auto\nend -- clump:auto\n'
    body=''.join(lines[738:768])
    assert body.count('private theorem ')==4
    for name in NAMES:
        assert 'private theorem '+name in body
    statement=''.join(lines[761:764])
    assert 'private theorem gens_eq_pz ' in statement
    candidate=(statement+'  funext i j b k Q ψ\n'
               +'  exact SerCopy.genSet_eq (a := x.o.Z) (oL x L).Z (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k Q ψ)\n')
    return {side:(prefix+text+suffix).encode() for side,text in [('control',''),('old',body),('new',candidate)]}
