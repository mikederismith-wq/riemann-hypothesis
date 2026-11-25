"""Derive the standalone and importer workloads from the two actual RH source graphs."""
from collections import defaultdict

T='Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.'
I='Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.'
DONOR=I+'ClassSumEq'
BUYER=T+'Lb2OfThetaTwistStatement'
EXTRA='Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace'
DROP='Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff'
OWNERS={DONOR,BUYER}
USERS={DONOR:{I+'ExistsNewTwistLamFull',T+'LayerUpStatement',T+'RowsAtStart'},
       BUYER:{T+'AllStagesAtMemberOfSpecializations',T+'MultiplicityBoundOfLocalComponents'}}
LEAVES=set.union(*USERS.values())
IMPACTED=OWNERS|LEAVES|{T+'FinitenessOfHyp'}


def cone(graph, roots):
    seen=set()
    todo=list(roots)
    while todo:
        name=todo.pop()
        if name in graph and name not in seen:
            seen.add(name)
            todo.extend(graph[name])
    return seen


def reverse(graph):
    rev=defaultdict(list)
    for name,imports in graph.items():
        for dep in imports:
            rev[dep].append(name)
    return rev


def verify(old,new):
    if old.keys()!=new.keys() or {m for m in old if old[m]!=new[m]}!=OWNERS:
        raise ValueError('incorrect initial dependency change')
    if new[DONOR]!=[n for n in old[DONOR] if n!=DROP] or new[BUYER].count(DONOR)!=1 or [n for n in new[BUYER] if n!=DONOR]!=old[BUYER]:
        raise ValueError('unexpected source import change')
    for label,graph in [('old',old),('new',new)]:
        rev=reverse(graph)
        for root,expected in USERS.items():
            actual=set(rev[root]); want=expected|({BUYER} if root==DONOR and label=='new' else set())
            if actual!=want:raise ValueError(f'wrong {label} direct users of {root}: {actual^want}')
        all_needed=cone(graph,LEAVES|OWNERS)
        if len(all_needed)!=17303 or all_needed&cone(rev,OWNERS)!=IMPACTED:
            raise ValueError('incorrect importer build plan')
    small=cone(old,OWNERS)|cone(new,OWNERS)
    old_solo=cone(old,{BUYER}); new_solo=cone(new,{BUYER})
    if len(small)!=5690 or len(old_solo)!=5663 or new_solo-old_solo!={DONOR,EXTRA} or old_solo-new_solo:
        raise ValueError('standalone buyer has unaccounted input costs')
    if (len(cone(old,{DONOR})),len(cone(new,{DONOR})))!=(1672,1401):
        raise ValueError('unexpected standalone donor closures')
    large=cone(old,LEAVES|OWNERS)|cone(new,LEAVES|OWNERS)
    if len(large)!=17303:raise ValueError('warm dependency identity differs between importer arms')
    return small-(OWNERS|{EXTRA}),large-IMPACTED
