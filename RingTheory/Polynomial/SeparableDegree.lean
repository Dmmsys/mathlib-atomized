/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `IsSeparableContraction`: is the condition that, for `g` a separable polynomial, we have that
  `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `HasSeparableContraction`: the condition of having a separable contraction
- `HasSeparableContraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `Irreducible.hasSeparableContraction`: any irreducible polynomial can be contracted
  to a separable polynomial
- `HasSeparableContraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `HasSeparableContraction.dvd_degree` and `HasSeparableContraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `IsSeparableContraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `HasSeparableContraction.degree`

## Tags

separable degree, degree, polynomial
-/

@[expose] public section

noncomputable section

namespace Polynomial

open Polynomial

section CommSemiring

variable {F : Type*} [CommSemiring F] (q : Nat)

/--
Definition of `IsSeparableContraction` / `IsSeparableContraction` 的定义

English:
definition IsSeparableContraction
  signature: (f : F[X]) (g : F[X])
  body: g.Separable ∧ exists m : Nat, expand F (q ^ m) g = f

中文:
定义 IsSeparableContraction
  签名: (f : F[X]) (g : F[X])
  定义体: g.Separable ∧ exists m : Nat, expand F (q ^ m) g = f

Depends on / 依赖: Separable, expand, g.Separable
-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ exists m : Nat, expand F (q ^ m) g = f

/--
Definition of `HasSeparableContraction` / `HasSeparableContraction` 的定义

English:
definition HasSeparableContraction
  signature: (f : F[X])
  body: exists g : F[X], IsSeparableContraction q f g

中文:
定义 HasSeparableContraction
  签名: (f : F[X])
  定义体: exists g : F[X], IsSeparableContraction q f g

Depends on / 依赖: IsSeparableContraction
-/
def HasSeparableContraction (f : F[X]) : Prop :=
  exists g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

/--
Definition of `HasSeparableContraction.contraction` / `HasSeparableContraction.contraction` 的定义

English:
definition HasSeparableContraction.contraction
  signature: : F[X]
  body: Classical.choose hf

中文:
定义 HasSeparableContraction.contraction
  签名: : F[X]
  定义体: Classical.choose hf

Depends on / 依赖: Classical, Classical.choose
-/
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf

/--
Definition of `HasSeparableContraction.degree` / `HasSeparableContraction.degree` 的定义

English:
definition HasSeparableContraction.degree
  signature: : Nat
  body: hf.contraction.natDegree

中文:
定义 HasSeparableContraction.degree
  签名: : 自然数
  定义体: hf.contraction.natDegree

Depends on / 依赖: contraction, hf.contraction.natDegree, natDegree
-/
def HasSeparableContraction.degree : Nat :=
  hf.contraction.natDegree

/--
theorem `HasSeparableContraction.isSeparableContraction` / 定理 `HasSeparableContraction.isSeparableContraction`

English:
theorem HasSeparableContraction.isSeparableContraction
  proof: Classical.choose_spec hf

中文:
定理 HasSeparableContraction.isSeparableContraction
  证明: Classical.choose_spec hf

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem HasSeparableContraction.isSeparableContraction :
    IsSeparableContraction q f hf.contraction := Classical.choose_spec hf

/--
theorem `IsSeparableContraction.dvd_degree'` / 定理 `IsSeparableContraction.dvd_degree'`

English:
theorem IsSeparableContraction.dvd_degree'
  given: {g} (hf : IsSeparableContraction q f g)
  proof: by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]

中文:
定理 IsSeparableContraction.dvd_degree'
  条件: {g} (hf : IsSeparableContraction q f g)
  证明: by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]

Depends on / 依赖: natDegree_expand
-/
theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    exists m : Nat, g.natDegree * q ^ m = f.natDegree := by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]

/--
theorem `HasSeparableContraction.dvd_degree'` / 定理 `HasSeparableContraction.dvd_degree'`

English:
theorem HasSeparableContraction.dvd_degree'
  statement: exists m : Nat, hf.degree * q ^ m = f.natDegree
  proof: (Classical.choose_spec hf).dvd_degree'

中文:
定理 HasSeparableContraction.dvd_degree'
  结论: 存在 m : 自然数, hf.degree * q ^ m = f.natDegree
  证明: (Classical.choose_spec hf).dvd_degree'

Depends on / 依赖: Classical, Classical.choose_spec, ContinuousConstVAdd, IsTopologicalAddGroup, basis.prod_self.tendsto_iff, choose_spec, continuous_iff_continuousAt, cts_add, dvd_degree, hasBasis_nhds, hasBasis_nhds_zero, map_eq_of_inverse, of_comm_of_nhds_zero, prod_self, tendsto_iff, valuat, valuation
-/
theorem HasSeparableContraction.dvd_degree' : exists m : Nat, hf.degree * q ^ m = f.natDegree :=
  (Classical.choose_spec hf).dvd_degree'

/--
theorem `HasSeparableContraction.dvd_degree` / 定理 `HasSeparableContraction.dvd_degree`

English:
theorem HasSeparableContraction.dvd_degree
  statement: hf.degree ∣ f.natDegree
  proof: let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

中文:
定理 HasSeparableContraction.dvd_degree
  结论: hf.degree ∣ f.natDegree
  证明: let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

Depends on / 依赖: Dvd.intro, dvd_degree, hf.dvd_degree
-/
theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

/--
theorem `HasSeparableContraction.eq_degree` / 定理 `HasSeparableContraction.eq_degree`

English:
theorem HasSeparableContraction.eq_degree
  given: {f : F[X]} (hf : HasSeparableContraction 1 f)
  proof: by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha]; rw [one_pow a]; rw [mul_one]

中文:
定理 HasSeparableContraction.eq_degree
  条件: {f : F[X]} (hf : HasSeparableContraction 1 f)
  证明: by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha]; rw [one_pow a]; rw [mul_one]

Depends on / 依赖: dvd_degree, hf.dvd_degree, mul_one, one_pow
-/
theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) :
    hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha]; rw [one_pow a]; rw [mul_one]

end CommSemiring

section Field

variable {F : Type*} [Field F]
variable (q : Nat) {f : F[X]} (hf : HasSeparableContraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial. -/
@[stacks 09H0]
/--
theorem `_root_.Irreducible.hasSeparableContraction` / 定理 `_root_.Irreducible.hasSeparableContraction`

English:
theorem _root_.Irreducible.hasSeparableContraction
  statement: (q : Nat) [hF : ExpChar F q] {f : F[X]}
  proof: by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.Prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩

中文:
定理 _root_.不可约.hasSeparableContraction
  结论: (q : 自然数) [hF : ExpChar F q] {f : F[X]}
  证明: by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.Prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩

Depends on / 依赖: exists_separable_of_irreducible, expand_one, irred.separable, ne_zero, pow_zero, q.Prime, separable
-/
theorem _root_.Irreducible.hasSeparableContraction (q : Nat) [hF : ExpChar F q] {f : F[X]}
    (irred : Irreducible f) : HasSeparableContraction q f := by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.Prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩

/--
theorem `contraction_degree_eq_or_insep` / 定理 `contraction_degree_eq_or_insep`

English:
theorem contraction_degree_eq_or_insep
  statement: [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : Nat)
  proof: by
  wlog hm : m <= m'
  · exact (this q g' g m' m h_expand.symm hg' hg (le_of_not_ge hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos (NeZero.pos q) m)] at h_expand
  subst h_expand
  rcases isUnit_or_eq_zero_of_separable_expand q s (NeZero

中文:
定理 contraction_degree_eq_or_insep
  结论: [hq : NeZero q] [特征p F q] (g g' : F[X]) (m m' : 自然数)
  证明: by
  wlog hm : m <= m'
  · exact (this q g' g m' m h_expand.symm hg' hg (le_of_not_ge hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos (NeZero.pos q) m)] at h_expand
  subst h_expand
  rcases isUnit_or_eq_zero_of_separable_expand q s (NeZero

Depends on / 依赖: NeZero, NeZero.pos, exists_add_of_le, expand_inj, expand_mul, h_expand, h_expand.symm, isUnit_or_eq_zero_of_separable_expand, le_of_not_ge, mul_one, natDegree_eq_zero_of_isUnit, natDegree_expand, pow_add, pow_pos, pow_zero, zero_mul
-/
theorem contraction_degree_eq_or_insep [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : Nat)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separable) (hg' : g'.Separable) :
    g.natDegree = g'.natDegree := by
  wlog hm : m <= m'
  · exact (this q g' g m' m h_expand.symm hg' hg (le_of_not_ge hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos (NeZero.pos q) m)] at h_expand
  subst h_expand
  rcases isUnit_or_eq_zero_of_separable_expand q s (NeZero.pos q) hg with (h | rfl)
  · rw [natDegree_expand, natDegree_eq_zero_of_isUnit h, zero_mul]
  · rw [natDegree_expand, pow_zero, mul_one]

/--
theorem `IsSeparableContraction.degree_eq` / 定理 `IsSeparableContraction.degree_eq`

English:
theorem IsSeparableContraction.degree_eq
  statement: [hF : ExpChar F q] (g : F[X])
  proof: by
  cases hF
  · rcases hg with ⟨_, m, hm⟩
    rw [one_pow]; rw [expand_one] at hm
    rw [hf.eq_degree]; rw [hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    obtain ⟨hg', m', hm'⟩ := Classical.choose_spec hf
    have : Fact q.Prime := ⟨by assumption⟩
    refine contraction_

中文:
定理 IsSeparableContraction.degree_eq
  结论: [hF : ExpChar F q] (g : F[X])
  证明: by
  cases hF
  · rcases hg with ⟨_, m, hm⟩
    rw [one_pow]; rw [expand_one] at hm
    rw [hf.eq_degree]; rw [hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    obtain ⟨hg', m', hm'⟩ := Classical.choose_spec hf
    have : Fact q.Prime := ⟨by assumption⟩
    refine contraction_

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, IsTopologicalRing, IsValuativeTopology, ValuativeRel, ValuativeRel.nonarchimedeanRing, _root_, _root_.IsValuativeTopology.isTopologicalRing, choose_spec, contraction_degree_eq_or_insep, convert, eq_degree, expand_one, hf.eq_degree, isTopologicalRing, nonarchimedeanRing, one_pow, q.Prime, toIsTopologicalRing
-/
theorem IsSeparableContraction.degree_eq [hF : ExpChar F q] (g : F[X])
    (hg : IsSeparableContraction q f g) : g.natDegree = hf.degree := by
  cases hF
  · rcases hg with ⟨_, m, hm⟩
    rw [one_pow]; rw [expand_one] at hm
    rw [hf.eq_degree]; rw [hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    obtain ⟨hg', m', hm'⟩ := Classical.choose_spec hf
    have : Fact q.Prime := ⟨by assumption⟩
    refine contraction_degree_eq_or_insep q g g' m m' ?_ hg hg'
    rw [hm]; rw [hm']

end Field

end Polynomial
