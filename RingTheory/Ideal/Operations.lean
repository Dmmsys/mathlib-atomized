/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Tactic.Order

/-!
# More operations on modules and ideals
-/

@[expose] public section

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`
  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open Module
open scoped Pointwise

namespace Submodule

/--
lemma `coe_span_smul` / 引理 `coe_span_smul`

English:
lemma coe_span_smul
  statement: {R' M' : Type*} [CommSemiring R'] [AddCommMonoid M'] [Module R' M']
  proof: set_smul_eq_of_le _ _ _
    (by rintro r n hr hn
        induction hr using Submodule.span_induction with
        | mem _ h => exact mem_set_smul_of_mem_mem h hn
        | zero => rw [zero_smul]; exact Submodule.zero_mem _
        | add _ _ _ _ ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr

中文:
引理 coe_span_smul
  结论: {R' M' : 类型} [交换半环 R'] [加法交换幺半群 M'] [模 R' M']
  证明: set_smul_eq_of_le _ _ _
    (by rintro r n hr hn
        induction hr using Submodule.span_induction with
        | mem _ h => exact mem_set_smul_of_mem_mem h hn
        | zero => rw [zero_smul]; exact Submodule.zero_mem _
        | add _ _ _ _ ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_smul, Finsupp, Finsupp.sum, Submodule, Submodule.add_mem, Submodule.span_induction, Submodule.sum_mem, Submodule.zero_mem, add_mem, add_smul, mem_set_smul_of_mem_mem, mem_span_set, mul_comm, mul_smu, mul_smul, set_smul_eq_of_le, smul_eq_mul, smul_sum
-/
lemma coe_span_smul {R' M' : Type*} [CommSemiring R'] [AddCommMonoid M'] [Module R' M']
    (s : Set R') (N : Submodule R' M') :
    (Ideal.span s : Set R') • N = s • N :=
  set_smul_eq_of_le _ _ _
    (by rintro r n hr hn
        induction hr using Submodule.span_induction with
        | mem _ h => exact mem_set_smul_of_mem_mem h hn
        | zero => rw [zero_smul]; exact Submodule.zero_mem _
        | add _ _ _ _ ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr ihs
        | smul _ _ hr =>
          rw [mem_span_set] at hr
          obtain ⟨c, hc, rfl⟩ := hr
          rw [Finsupp.sum]; rw [Finset.smul_sum]; rw [Finset.sum_smul]
          refine Submodule.sum_mem _ fun i hi => ?_
          rw [← mul_smul]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_smul]
exact mem_set_smul_of_mem_mem (hc hi) Submodule.smul_mem _ _ hn) <|
    set_smul_mono_left _ Submodule.subset_span

/--
lemma `span_singleton_toAddSubgroup_eq_zmultiples` / 引理 `span_singleton_toAddSubgroup_eq_zmultiples`

English:
lemma span_singleton_toAddSubgroup_eq_zmultiples
  given: {M : Type*} [AddCommGroup M] (a : M)
  proof: by
  ext i
  simp [Submodule.mem_span_singleton, AddSubgroup.mem_zmultiples_iff]

中文:
引理 span_singleton_toAddSubgroup_eq_zmultiples
  条件: {M : 类型} [加法交换群 M] (a : M)
  证明: by
  ext i
  simp [Submodule.mem_span_singleton, AddSubgroup.mem_zmultiples_iff]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, Submodule, Submodule.mem_span_singleton, continuous_def, mem_span_singleton, mem_zmultiples_iff
-/
lemma span_singleton_toAddSubgroup_eq_zmultiples {M : Type*} [AddCommGroup M] (a : M) :
    (span Int ({a} : Set M)).toAddSubgroup = AddSubgroup.zmultiples a := by
  ext i
  simp [Submodule.mem_span_singleton, AddSubgroup.mem_zmultiples_iff]

/--
lemma `_root_.Ideal.span_singleton_toAddSubgroup_eq_zmultiples` / 引理 `_root_.Ideal.span_singleton_toAddSubgroup_eq_zmultiples`

English:
lemma _root_.Ideal.span_singleton_toAddSubgroup_eq_zmultiples
  given: (a : Int)
  proof: Submodule.span_singleton_toAddSubgroup_eq_zmultiples _

中文:
引理 _root_.理想.span_singleton_toAddSubgroup_eq_zmultiples
  条件: (a : 整数)
  证明: Submodule.span_singleton_toAddSubgroup_eq_zmultiples _
-/
@[simp] lemma _root_.Ideal.span_singleton_toAddSubgroup_eq_zmultiples (a : Int) :
    (Ideal.span {a}).toAddSubgroup = AddSubgroup.zmultiples a :=
  Submodule.span_singleton_toAddSubgroup_eq_zmultiples _

variable {R : Type u} {M : Type v} {M' F G : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `_root_.Ideal.smul_eq_mul` / 定理 `_root_.Ideal.smul_eq_mul`

English:
theorem _root_.Ideal.smul_eq_mul
  given: (I J : Ideal R)
  statement: I • J = I * J
  proof: rfl

中文:
定理 _root_.理想.smul_eq_mul
  条件: (I J : 理想 R)
  结论: I • J = I * J
  证明: rfl
-/
protected theorem _root_.Ideal.smul_eq_mul (I J : Ideal R) : I • J = I * J :=
  rfl

variable {I J : Ideal R} {N : Submodule R M}

/--
theorem `smul_le_right` / 定理 `smul_le_right`

English:
theorem smul_le_right
  statement: I • N <= N
  proof: smul_le.2 fun r _ _ => N.smul_mem r

中文:
定理 smul_le_right
  结论: I • N <= N
  证明: smul_le.2 fun r _ _ => N.smul_mem r

Depends on / 依赖: N.smul_mem, smul_le, smul_mem
-/
theorem smul_le_right : I • N <= N :=
  smul_le.2 fun r _ _ => N.smul_mem r

/--
theorem `map_le_smul_top` / 定理 `map_le_smul_top`

English:
theorem map_le_smul_top
  given: (I : Ideal R) (f : R ->ₗ[R] M)
  proof: by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_one y]; rw [← smul_eq_mul]; rw [f.map_smul]
  exact smul_mem_smul hy mem_top

中文:
定理 map_le_smul_top
  条件: (I : 理想 R) (f : R ->ₗ[R] M)
  证明: by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_one y]; rw [← smul_eq_mul]; rw [f.map_smul]
  exact smul_mem_smul hy mem_top

Depends on / 依赖: f.map_smul, map_smul, mem_top, mul_one, smul_eq_mul, smul_mem_smul
-/
theorem map_le_smul_top (I : Ideal R) (f : R ->ₗ[R] M) :
    Submodule.map f I <= I • (⊤ : Submodule R M) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_one y]; rw [← smul_eq_mul]; rw [f.map_smul]
  exact smul_mem_smul hy mem_top

variable (I J N)

@[simp]
/--
theorem `top_smul` / 定理 `top_smul`

English:
theorem top_smul
  statement: (⊤ : Ideal R) • N = N
  proof: le_antisymm smul_le_right fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri

中文:
定理 top_smul
  结论: (⊤ : 理想 R) • N = N
  证明: le_antisymm smul_le_right fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri

Depends on / 依赖: le_antisymm, mem_top, one_smul, smul_le_right, smul_mem_smul
-/
theorem top_smul : (⊤ : Ideal R) • N = N :=
  le_antisymm smul_le_right fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri

/--
theorem `mul_smul` / 定理 `mul_smul`

English:
theorem mul_smul
  statement: (I * J) • N = I • J • N
  proof: Submodule.smul_assoc _ _ _

中文:
定理 mul_smul
  结论: (I * J) • N = I • J • N
  证明: Submodule.smul_assoc _ _ _
-/
protected theorem mul_smul : (I * J) • N = I • J • N :=
  Submodule.smul_assoc _ _ _

/--
theorem `mem_of_span_top_of_smul_mem` / 定理 `mem_of_span_top_of_smul_mem`

English:
theorem mem_of_span_top_of_smul_mem
  statement: (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
  proof: by
  suffices LinearMap.range (LinearMap.toSpanSingleton R M x) <= M' by
    rw [← LinearMap.toSpanSingleton_apply_one R M x]
    exact this (LinearMap.mem_range_self _ 1)
  rw [LinearMap.range_eq_map]; rw [← hs]; rw [map_le_iff_le_comap]; rw [Ideal.span]; rw [span_le]
  exact fun r hr => H ⟨r, hr⟩

中文:
定理 mem_of_span_top_of_smul_mem
  结论: (M' : 子模 R M) (s : 集合 R) (hs : 理想.span s = ⊤) (x : M)
  证明: by
  suffices LinearMap.range (LinearMap.toSpanSingleton R M x) <= M' by
    rw [← LinearMap.toSpanSingleton_apply_one R M x]
    exact this (LinearMap.mem_range_self _ 1)
  rw [LinearMap.range_eq_map]; rw [← hs]; rw [map_le_iff_le_comap]; rw [Ideal.span]; rw [span_le]
  exact fun r hr => H ⟨r, hr⟩

Depends on / 依赖: Ideal.span, LinearMap, LinearMap.mem_range_self, LinearMap.range, LinearMap.range_eq_map, LinearMap.toSpanSingleton, LinearMap.toSpanSingleton_apply_one, map_le_iff_le_comap, mem_range_self, range_eq_map, span_le, toSpanSingleton, toSpanSingleton_apply_one
-/
theorem mem_of_span_top_of_smul_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
    (H : forall r : s, (r : R) • x in M') : x in M' := by
  suffices LinearMap.range (LinearMap.toSpanSingleton R M x) <= M' by
    rw [← LinearMap.toSpanSingleton_apply_one R M x]
    exact this (LinearMap.mem_range_self _ 1)
  rw [LinearMap.range_eq_map]; rw [← hs]; rw [map_le_iff_le_comap]; rw [Ideal.span]; rw [span_le]
  exact fun r hr => H ⟨r, hr⟩

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

@[simp]
/--
theorem `map_smul''` / 定理 `map_smul''`

English:
theorem map_smul''
  given: (f : M ->ₗ[R] M')
  statement: (I • N).map f = I • N.map f
  proof: le_antisymm
    (map_le_iff_le_comap.2 <|
      smul_le.2 fun r hr n hn =>
        show f (r • n) in I • N.map f from
          (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr _ hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_

中文:
定理 map_smul''
  条件: (f : M ->ₗ[R] M')
  结论: (I • N).map f = I • N.map f
  证明: le_antisymm
    (map_le_iff_le_comap.2 <|
      smul_le.2 fun r hr n hn =>
        show f (r • n) in I • N.map f from
          (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr _ hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_

Depends on / 依赖: N.map, f.map_smul, le_antisymm, map_le_iff_le_comap, map_smul, mem_map, mem_map_of_mem, smul_le, smul_mem_smul
-/
theorem map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I • N.map f :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      smul_le.2 fun r hr n hn =>
        show f (r • n) in I • N.map f from
          (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr _ hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

/--
theorem `mem_smul_top_iff` / 定理 `mem_smul_top_iff`

English:
theorem mem_smul_top_iff
  given: (N : Submodule R M) (x : N)
  proof: by
  have : Submodule.map N.subtype (I • ⊤) = I • N := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]
  simp [← this, -map_smul'']

@[simp]

中文:
定理 mem_smul_top_iff
  条件: (N : 子模 R M) (x : N)
  证明: by
  have : Submodule.map N.subtype (I • ⊤) = I • N := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]
  simp [← this, -map_smul'']

@[simp]

Depends on / 依赖: N.subtype, Submodule, Submodule.map, Submodule.map_smul, Submodule.map_top, Submodule.range_subtype, map_smul, map_top, range_subtype, subtype
-/
theorem mem_smul_top_iff (N : Submodule R M) (x : N) :
    x in I • (⊤ : Submodule R N) ↔ (x : M) in I • N := by
  have : Submodule.map N.subtype (I • ⊤) = I • N := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]
  simp [← this, -map_smul'']

@[simp]
/--
theorem `smul_comap_le_comap_smul` / 定理 `smul_comap_le_comap_smul`

English:
theorem smul_comap_le_comap_smul
  given: (f : M ->ₗ[R] M') (S : Submodule R M') (I : Ideal R)
  proof: by
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx

中文:
定理 smul_comap_le_comap_smul
  条件: (f : M ->ₗ[R] M') (S : 子模 R M') (I : 理想 R)
  证明: by
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx

Depends on / 依赖: Submodule, Submodule.mem_comap, Submodule.smul_le.mpr, Submodule.smul_mem_smul, f.map_smul, map_smul, mem_comap, smul_le, smul_mem_smul
-/
theorem smul_comap_le_comap_smul (f : M ->ₗ[R] M') (S : Submodule R M') (I : Ideal R) :
    I • S.comap f <= (I • S).comap f := by
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx

/--
lemma `comap_smul''` / 引理 `comap_smul''`

English:
lemma comap_smul''
  statement: {f : M ->ₗ[R] M'} (hf : Function.Injective f) {p : Submodule R M'}
  proof: by
  refine le_antisymm ?_ (by simp)
  conv_lhs => rw [← Submodule.map_comap_eq_self hp, ← Submodule.map_smul'']
  rw [Submodule.comap_map_eq_of_injective hf]

中文:
引理 comap_smul''
  结论: {f : M ->ₗ[R] M'} (hf : 函数.单射 f) {p : 子模 R M'}
  证明: by
  refine le_antisymm ?_ (by simp)
  conv_lhs => rw [← Submodule.map_comap_eq_self hp, ← Submodule.map_smul'']
  rw [Submodule.comap_map_eq_of_injective hf]

Depends on / 依赖: Submodule, Submodule.comap_map_eq_of_injective, Submodule.map_comap_eq_self, Submodule.map_smul, comap_map_eq_of_injective, conv_lhs, le_antisymm, map_comap_eq_self, map_smul
-/
lemma comap_smul'' {f : M ->ₗ[R] M'} (hf : Function.Injective f) {p : Submodule R M'}
    (hp : p <= LinearMap.range f) {I : Ideal R} :
    Submodule.comap f (I • p) = I • Submodule.comap f p := by
  refine le_antisymm ?_ (by simp)
  conv_lhs => rw [← Submodule.map_comap_eq_self hp, ← Submodule.map_smul'']
  rw [Submodule.comap_map_eq_of_injective hf]

variable {I}

/--
theorem `mem_smul_span_singleton` / 定理 `mem_smul_span_singleton`

English:
theorem mem_smul_span_singleton
  given: [I.IsTwoSided] {m : M} {x : M}
  proof: ⟨fun hx =>
    smul_induction_on hx
      (fun r hri _ hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩,
    fun ⟨_, 

中文:
定理 mem_smul_span_singleton
  条件: [I.是TwoSided] {m : M} {x : M}
  证明: ⟨fun hx =>
    smul_induction_on hx
      (fun r hri _ hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩,
    fun ⟨_, 

Depends on / 依赖: I.add_mem, I.mul_mem_right, Set.mem_singleton, add_mem, add_smul, continuousAt_const, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, mem_singleton, mem_span_singleton, mul_mem_right, mul_smul, smul_induction_on, smul_mem_smul, subset_span
-/
theorem mem_smul_span_singleton [I.IsTwoSided] {m : M} {x : M} :
    x in I • span R ({m} : Set M) ↔ exists y in I, y • m = x :=
  ⟨fun hx =>
    smul_induction_on hx
      (fun r hri _ hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩,
    fun ⟨_, hyi, hy⟩ => hy ▸ smul_mem_smul hyi (subset_span <| Set.mem_singleton m)⟩

variable (S : Set R) (T : Set M)

/--
theorem `span_smul_span` / 定理 `span_smul_span`

English:
theorem span_smul_span
  given: [(Ideal.span S).IsTwoSided]
  proof: le_antisymm (smul_le.mpr fun r hr m hm => by
    revert r
    refine span_induction (fun m hm r hr => span_induction
      (fun r hr => subset_span ⟨r, hr, m, hm, rfl⟩)
      (by rw [zero_smul]; exact zero_mem _)
      (fun _ _ _ _ h₁ h₂ => by rw [add_smul]; exact add_mem h₁ h₂)
      (fun _ _ _ h =

中文:
定理 span_smul_span
  条件: [(理想.span S).是TwoSided]
  证明: le_antisymm (smul_le.mpr fun r hr m hm => by
    revert r
    refine span_induction (fun m hm r hr => span_induction
      (fun r hr => subset_span ⟨r, hr, m, hm, rfl⟩)
      (by rw [zero_smul]; exact zero_mem _)
      (fun _ _ _ _ h₁ h₂ => by rw [add_smul]; exact add_mem h₁ h₂)
      (fun _ _ _ h =

Depends on / 依赖: add_mem, add_smul, le_antisymm, mul_smul, revert, smul_add, smul_assoc, smul_le, smul_le.mpr, smul_mem, smul_zero, span_induction, subset_span, zero_mem, zero_smul
-/
theorem span_smul_span [(Ideal.span S).IsTwoSided] :
    Ideal.span S • span R T = span R (S • T) :=
  le_antisymm (smul_le.mpr fun r hr m hm => by
    revert r
    refine span_induction (fun m hm r hr => span_induction
      (fun r hr => subset_span ⟨r, hr, m, hm, rfl⟩)
      (by rw [zero_smul]; exact zero_mem _)
      (fun _ _ _ _ h₁ h₂ => by rw [add_smul]; exact add_mem h₁ h₂)
      (fun _ _ _ h => by rw [smul_assoc]; exact smul_mem _ _ h) hr)
      (fun _ _ => by rw [smul_zero]; exact zero_mem _)
      (fun _ _ _ _ h₁ h₂ r hr => by rw [smul_add]; exact add_mem (h₁ r hr) (h₂ r hr))
      (fun r' m hm mem r hr => by rw [← mul_smul]; exact mem _ (Ideal.mul_mem_right _ _ hr)) hm) <|
  span_le.mpr fun m => by
    rintro ⟨s, hs, t, ht, rfl⟩
    exact smul_mem_smul (subset_span hs) (subset_span ht)

variable [I.IsTwoSided]

/--
theorem `mem_smul_span` / 定理 `mem_smul_span`

English:
theorem mem_smul_span
  given: {s : Set M} {x : M}
  proof: by
  rw [← I.span_eq] at *
  rw [Submodule.span_smul_span]; rw [I.span_eq]

中文:
定理 mem_smul_span
  条件: {s : 集合 M} {x : M}
  证明: by
  rw [← I.span_eq] at *
  rw [Submodule.span_smul_span]; rw [I.span_eq]

Depends on / 依赖: I.span_eq, Submodule, Submodule.span_smul_span, span_eq, span_smul_span
-/
theorem mem_smul_span {s : Set M} {x : M} :
    x in I • Submodule.span R s ↔ x in Submodule.span R ((I : Set R) • s) := by
  rw [← I.span_eq] at *
  rw [Submodule.span_smul_span]; rw [I.span_eq]

variable (I)

/--
theorem `mem_ideal_smul_span_iff_exists_sum` / 定理 `mem_ideal_smul_span_iff_exists_sum`

English:
theorem mem_ideal_smul_span_iff_exists_sum
  given: {ι : Type*} (f : ι -> M) (x : M)
  proof: by
  constructor; swap
  · rintro ⟨a, ha, rfl⟩
exact Submodule.sum_mem _ fun c _ => smul_mem_smul (ha c) subset_span Set.mem_range_self _
  refine fun hx => span_induction ?_ ?_ ?_ ?_ (mem_smul_span.mp hx)
  · rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i y, fun j => ?_, ?_⟩
    · 

中文:
定理 mem_ideal_smul_span_iff_存在_sum
  条件: {ι : 类型} (f : ι -> M) (x : M)
  证明: by
  constructor; swap
  · rintro ⟨a, ha, rfl⟩
exact Submodule.sum_mem _ fun c _ => smul_mem_smul (ha c) subset_span Set.mem_range_self _
  refine fun hx => span_induction ?_ ?_ ?_ ?_ (mem_smul_span.mp hx)
  · rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i y, fun j => ?_, ?_⟩
    · 

Depends on / 依赖: Classical, Classical.decEq, Finsupp, Finsupp.single, Finsupp.single_apply, Finsupp.sum_single_index, Finsupp.sum_ze, I.zero_mem, Set.mem_range_self, Submodule, Submodule.sum_mem, mem_range_self, mem_smul_span, mem_smul_span.mp, single, single_apply, smul_mem_smul, span_induction, split_ifs, subset_span
-/
theorem mem_ideal_smul_span_iff_exists_sum {ι : Type*} (f : ι -> M) (x : M) :
    x in I • span R (Set.range f) ↔
      exists (a : ι ->₀ R) (_ : forall i, a i in I), (a.sum fun i c => c • f i) = x := by
  constructor; swap
  · rintro ⟨a, ha, rfl⟩
exact Submodule.sum_mem _ fun c _ => smul_mem_smul (ha c) subset_span Set.mem_range_self _
  refine fun hx => span_induction ?_ ?_ ?_ ?_ (mem_smul_span.mp hx)
  · rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i y, fun j => ?_, ?_⟩
    · let := Classical.decEq ι
      rw [Finsupp.single_apply]
      split_ifs
      · assumption
      · exact I.zero_mem
    refine @Finsupp.sum_single_index ι R M _ _ i _ (fun i y => y • f i) ?_
    simp
  · exact ⟨0, fun _ => I.zero_mem, Finsupp.sum_zero_index⟩
  · rintro x y - - ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩
    refine ⟨ax + ay, fun i => I.add_mem (hax i) (hay i), Finsupp.sum_add_index' ?_ ?_⟩ <;>
      intros <;> simp only [zero_smul, add_smul]
  · rintro c x - ⟨a, ha, rfl⟩
    refine ⟨c • a, fun i => I.mul_mem_left c (ha i), ?_⟩
    rw [Finsupp.sum_smul_index]; rw [Finsupp.smul_sum] <;> intros <;> simp only [zero_smul, mul_smul]

/--
theorem `mem_ideal_smul_span_iff_exists_sum'` / 定理 `mem_ideal_smul_span_iff_exists_sum'`

English:
theorem mem_ideal_smul_span_iff_exists_sum'
  given: {ι : Type*} (s : Set ι) (f : ι -> M) (x : M)
  proof: by
  rw [← Submodule.mem_ideal_smul_span_iff_exists_sum]; rw [← Set.image_eq_range]

中文:
定理 mem_ideal_smul_span_iff_存在_sum'
  条件: {ι : 类型} (s : 集合 ι) (f : ι -> M) (x : M)
  证明: by
  rw [← Submodule.mem_ideal_smul_span_iff_exists_sum]; rw [← Set.image_eq_range]

Depends on / 依赖: Set.image_eq_range, Submodule, Submodule.mem_ideal_smul_span_iff_exists_sum, image_eq_range, mem_ideal_smul_span_iff_exists_sum
-/
theorem mem_ideal_smul_span_iff_exists_sum' {ι : Type*} (s : Set ι) (f : ι -> M) (x : M) :
    x in I • span R (f '' s) ↔
    exists (a : s ->₀ R) (_ : forall i, a i in I), (a.sum fun i c => c • f i) = x := by
  rw [← Submodule.mem_ideal_smul_span_iff_exists_sum]; rw [← Set.image_eq_range]

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

open scoped Pointwise

variable {I : Ideal R} {N : Submodule R M}

/--
theorem `smul_eq_map₂` / 定理 `smul_eq_map₂`

English:
theorem smul_eq_map₂
  statement: I • N = Submodule.map₂ (LinearMap.lsmul R M) I N
  proof: le_antisymm (smul_le.mpr fun _m hm _n => Submodule.apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => smul_mem_smul hm)

中文:
定理 smul_eq_map₂
  结论: I • N = 子模.map₂ (线性映射.lsmul R M) I N
  证明: le_antisymm (smul_le.mpr fun _m hm _n => Submodule.apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => smul_mem_smul hm)

Depends on / 依赖: Submodule, Submodule.apply_mem_map, _le.mpr, le_antisymm, smul_le, smul_le.mpr, smul_mem_smul
-/
theorem smul_eq_map₂ : I • N = Submodule.map₂ (LinearMap.lsmul R M) I N :=
  le_antisymm (smul_le.mpr fun _m hm _n => Submodule.apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => smul_mem_smul hm)

variable (S : Set R) (T : Set M)

/--
theorem `ideal_span_singleton_smul` / 定理 `ideal_span_singleton_smul`

English:
theorem ideal_span_singleton_smul
  given: (r : R) (N : Submodule R M)
  proof: by
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa using span_eq (r • N)

中文:
定理 ideal_span_singleton_smul
  条件: (r : R) (N : 子模 R M)
  证明: by
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa using span_eq (r • N)

Depends on / 依赖: conv_lhs, span_eq, span_smul_span
-/
theorem ideal_span_singleton_smul (r : R) (N : Submodule R M) :
    (Ideal.span {r} : Ideal R) • N = r • N := by
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa using span_eq (r • N)

/--
theorem `mem_of_span_eq_top_of_smul_pow_mem` / 定理 `mem_of_span_eq_top_of_smul_pow_mem`

English:
theorem mem_of_span_eq_top_of_smul_pow_mem
  statement: (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤)
  proof: by
  choose f hf using H
  apply M'.mem_of_span_top_of_smul_mem _ (Ideal.span_range_pow_eq_top s hs f)
  rintro ⟨_, r, hr, rfl⟩
  exact hf r

中文:
定理 mem_of_span_eq_top_of_smul_pow_mem
  结论: (M' : 子模 R M) (s : 集合 R) (hs : 理想.span s = ⊤)
  证明: by
  choose f hf using H
  apply M'.mem_of_span_top_of_smul_mem _ (Ideal.span_range_pow_eq_top s hs f)
  rintro ⟨_, r, hr, rfl⟩
  exact hf r

Depends on / 依赖: Ideal.span_range_pow_eq_top, mem_of_span_top_of_smul_mem, span_range_pow_eq_top
-/
theorem mem_of_span_eq_top_of_smul_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤)
    (x : M) (H : forall r : s, exists n : Nat, ((r : R) ^ n : R) • x in M') : x in M' := by
  choose f hf using H
  apply M'.mem_of_span_top_of_smul_mem _ (Ideal.span_range_pow_eq_top s hs f)
  rintro ⟨_, r, hr, rfl⟩
  exact hf r

open scoped Pointwise in
@[simp]
/--
theorem `map_pointwise_smul` / 定理 `map_pointwise_smul`

English:
theorem map_pointwise_smul
  given: (r : R) (N : Submodule R M) (f : M ->ₗ[R] M')
  proof: by
  simp_rw [← ideal_span_singleton_smul, map_smul'']

中文:
定理 map_pointwise_smul
  条件: (r : R) (N : 子模 R M) (f : M ->ₗ[R] M')
  证明: by
  simp_rw [← ideal_span_singleton_smul, map_smul'']

Depends on / 依赖: ideal_span_singleton_smul, map_smul, simp_rw
-/
theorem map_pointwise_smul (r : R) (N : Submodule R M) (f : M ->ₗ[R] M') :
    (r • N).map f = r • N.map f := by
  simp_rw [← ideal_span_singleton_smul, map_smul'']

end CommSemiring

end Submodule

namespace Ideal

section Add

variable {R : Type u} [Semiring R]

@[simp]
/--
theorem `add_eq_sup` / 定理 `add_eq_sup`

English:
theorem add_eq_sup
  given: {I J : Ideal R}
  statement: I + J = I ⊔ J
  proof: rfl

@[simp]

中文:
定理 add_eq_sup
  条件: {I J : 理想 R}
  结论: I + J = I ⊔ J
  证明: rfl

@[simp]
-/
theorem add_eq_sup {I J : Ideal R} : I + J = I ⊔ J :=
  rfl

@[simp]
/--
theorem `zero_eq_bot` / 定理 `zero_eq_bot`

English:
theorem zero_eq_bot
  statement: (0 : Ideal R) = ⊥
  proof: rfl

@[simp]

中文:
定理 zero_eq_bot
  结论: (0 : 理想 R) = ⊥
  证明: rfl

@[simp]
-/
theorem zero_eq_bot : (0 : Ideal R) = ⊥ :=
  rfl

@[simp]
/--
theorem `sum_eq_sup` / 定理 `sum_eq_sup`

English:
theorem sum_eq_sup
  given: {ι : Type*} (s : Finset ι) (f : ι -> Ideal R)
  statement: s.sum f = s.sup f
  proof: rfl

中文:
定理 sum_eq_sup
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 理想 R)
  结论: s.求和 f = s.上确界 f
  证明: rfl
-/
theorem sum_eq_sup {ι : Type*} (s : Finset ι) (f : ι -> Ideal R) : s.sum f = s.sup f :=
  rfl

end Add

section Semiring

variable {R : Type u} [Semiring R] {I J K L : Ideal R}

@[simp, grind =]
/--
theorem `one_eq_top` / 定理 `one_eq_top`

English:
theorem one_eq_top
  statement: (1 : Ideal R) = ⊤
  proof: by
  rw [Submodule.one_eq_span]; rw [← Ideal.span]; rw [Ideal.span_singleton_one]

中文:
定理 one_eq_top
  结论: (1 : 理想 R) = ⊤
  证明: by
  rw [Submodule.one_eq_span]; rw [← Ideal.span]; rw [Ideal.span_singleton_one]

Depends on / 依赖: Ideal.span, Ideal.span_singleton_one, Submodule, Submodule.one_eq_span, one_eq_span, span_singleton_one
-/
theorem one_eq_top : (1 : Ideal R) = ⊤ := by
  rw [Submodule.one_eq_span]; rw [← Ideal.span]; rw [Ideal.span_singleton_one]

/--
theorem `add_eq_one_iff` / 定理 `add_eq_one_iff`

English:
theorem add_eq_one_iff
  statement: I + J = 1 ↔ exists i in I, exists j in J, i + j = 1
  proof: by
  rw [one_eq_top]; rw [eq_top_iff_one]; rw [add_eq_sup]; rw [Submodule.mem_sup]

中文:
定理 add_eq_one_iff
  结论: I + J = 1 ↔ 存在 i in I, 存在 j in J, i + j = 1
  证明: by
  rw [one_eq_top]; rw [eq_top_iff_one]; rw [add_eq_sup]; rw [Submodule.mem_sup]

Depends on / 依赖: Submodule, Submodule.mem_sup, add_eq_sup, eq_top_iff_one, mem_sup, one_eq_top
-/
theorem add_eq_one_iff : I + J = 1 ↔ exists i in I, exists j in J, i + j = 1 := by
  rw [one_eq_top]; rw [eq_top_iff_one]; rw [add_eq_sup]; rw [Submodule.mem_sup]

/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  given: {r s} (hr : r in I) (hs : s in J)
  statement: r * s in I * J
  proof: Submodule.smul_mem_smul hr hs

中文:
定理 mul_mem_mul
  条件: {r s} (hr : r in I) (hs : s in J)
  结论: r * s in I * J
  证明: Submodule.smul_mem_smul hr hs

Depends on / 依赖: Submodule, Submodule.smul_mem_smul, smul_mem_smul
-/
theorem mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s in I * J :=
  Submodule.smul_mem_smul hr hs

/--
theorem `bot_pow` / 定理 `bot_pow`

English:
theorem bot_pow
  given: {n : Nat} (hn : n != 0)
  proof: Submodule.bot_pow hn

中文:
定理 bot_pow
  条件: {n : 自然数} (hn : n != 0)
  证明: Submodule.bot_pow hn

Depends on / 依赖: Submodule, Submodule.bot_pow, bot_pow
-/
theorem bot_pow {n : Nat} (hn : n != 0) :
    (⊥ : Ideal R) ^ n = ⊥ := Submodule.bot_pow hn

/--
theorem `pow_mem_pow` / 定理 `pow_mem_pow`

English:
theorem pow_mem_pow
  given: {x : R} (hx : x in I) (n : Nat)
  statement: x ^ n in I ^ n
  proof: Submodule.pow_mem_pow _ hx _

中文:
定理 pow_mem_pow
  条件: {x : R} (hx : x in I) (n : 自然数)
  结论: x ^ n in I ^ n
  证明: Submodule.pow_mem_pow _ hx _

Depends on / 依赖: Submodule, Submodule.pow_mem_pow, pow_mem_pow
-/
theorem pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n in I ^ n :=
  Submodule.pow_mem_pow _ hx _

/--
theorem `mul_le` / 定理 `mul_le`

English:
theorem mul_le
  statement: I * J <= K ↔ forall r in I, forall s in J, r * s in K
  proof: Submodule.smul_le

中文:
定理 mul_le
  结论: I * J <= K ↔ 对任意 r in I, 对任意 s in J, r * s in K
  证明: Submodule.smul_le

Depends on / 依赖: Submodule, Submodule.smul_le, smul_le
-/
theorem mul_le : I * J <= K ↔ forall r in I, forall s in J, r * s in K :=
  Submodule.smul_le

/--
theorem `mul_le_right` / 定理 `mul_le_right`

English:
theorem mul_le_right
  statement: I * J <= J
  proof: mul_le.2 fun _ _ _ => J.mul_mem_left _

@[simp]

中文:
定理 mul_le_right
  结论: I * J <= J
  证明: mul_le.2 fun _ _ _ => J.mul_mem_left _

@[simp]

Depends on / 依赖: J.mul_mem_left, mul_le, mul_mem_left
-/
theorem mul_le_right : I * J <= J :=
  mul_le.2 fun _ _ _ => J.mul_mem_left _

@[simp]
/--
theorem `sup_mul_left_self` / 定理 `sup_mul_left_self`

English:
theorem sup_mul_left_self
  statement: I ⊔ J * I = I
  proof: sup_eq_left.2 mul_le_right

@[simp]

中文:
定理 sup_mul_left_self
  结论: I ⊔ J * I = I
  证明: sup_eq_left.2 mul_le_right

@[simp]

Depends on / 依赖: mul_le_right, sup_eq_left
-/
theorem sup_mul_left_self : I ⊔ J * I = I :=
  sup_eq_left.2 mul_le_right

@[simp]
/--
theorem `mul_left_self_sup` / 定理 `mul_left_self_sup`

English:
theorem mul_left_self_sup
  statement: J * I ⊔ I = I
  proof: sup_eq_right.2 mul_le_right

中文:
定理 mul_left_self_sup
  结论: J * I ⊔ I = I
  证明: sup_eq_right.2 mul_le_right

Depends on / 依赖: mul_le_right, sup_eq_right
-/
theorem mul_left_self_sup : J * I ⊔ I = I :=
  sup_eq_right.2 mul_le_right

/--
theorem `mul_le_left` / 定理 `mul_le_left`

English:
theorem mul_le_left
  given: [I.IsTwoSided]
  statement: I * J <= I
  proof: mul_le.2 fun _ hr _ _ => I.mul_mem_right _ hr

@[simp]

中文:
定理 mul_le_left
  条件: [I.是TwoSided]
  结论: I * J <= I
  证明: mul_le.2 fun _ hr _ _ => I.mul_mem_right _ hr

@[simp]

Depends on / 依赖: I.mul_mem_right, mul_le, mul_mem_right
-/
theorem mul_le_left [I.IsTwoSided] : I * J <= I :=
  mul_le.2 fun _ hr _ _ => I.mul_mem_right _ hr

@[simp]
/--
theorem `sup_mul_right_self` / 定理 `sup_mul_right_self`

English:
theorem sup_mul_right_self
  given: [I.IsTwoSided]
  statement: I ⊔ I * J = I
  proof: sup_eq_left.2 mul_le_left

@[simp]

中文:
定理 sup_mul_right_self
  条件: [I.是TwoSided]
  结论: I ⊔ I * J = I
  证明: sup_eq_left.2 mul_le_left

@[simp]

Depends on / 依赖: mul_le_left, sup_eq_left
-/
theorem sup_mul_right_self [I.IsTwoSided] : I ⊔ I * J = I :=
  sup_eq_left.2 mul_le_left

@[simp]
/--
theorem `mul_right_self_sup` / 定理 `mul_right_self_sup`

English:
theorem mul_right_self_sup
  given: [I.IsTwoSided]
  statement: I * J ⊔ I = I
  proof: sup_eq_right.2 mul_le_left

中文:
定理 mul_right_self_sup
  条件: [I.是TwoSided]
  结论: I * J ⊔ I = I
  证明: sup_eq_right.2 mul_le_left

Depends on / 依赖: mul_le_left, sup_eq_right
-/
theorem mul_right_self_sup [I.IsTwoSided] : I * J ⊔ I = I :=
  sup_eq_right.2 mul_le_left

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  statement: I * J * K = I * (J * K)
  proof: Submodule.smul_assoc I J K

中文:
定理 mul_assoc
  结论: I * J * K = I * (J * K)
  证明: Submodule.smul_assoc I J K
-/
protected theorem mul_assoc : I * J * K = I * (J * K) :=
  Submodule.smul_assoc I J K

variable (I)

/--
theorem `mul_bot` / 定理 `mul_bot`

English:
theorem mul_bot
  statement: I * ⊥ = ⊥
  proof: by simp

中文:
定理 mul_bot
  结论: I * ⊥ = ⊥
  证明: by simp
-/
theorem mul_bot : I * ⊥ = ⊥ := by simp

/--
theorem `bot_mul` / 定理 `bot_mul`

English:
theorem bot_mul
  statement: ⊥ * I = ⊥
  proof: by simp

@[simp]

中文:
定理 bot_mul
  结论: ⊥ * I = ⊥
  证明: by simp

@[simp]
-/
theorem bot_mul : ⊥ * I = ⊥ := by simp

@[simp]
/--
theorem `top_mul` / 定理 `top_mul`

English:
theorem top_mul
  statement: ⊤ * I = I
  proof: Submodule.top_smul I

中文:
定理 top_mul
  结论: ⊤ * I = I
  证明: Submodule.top_smul I

Depends on / 依赖: Submodule, Submodule.top_smul, top_smul
-/
theorem top_mul : ⊤ * I = I :=
  Submodule.top_smul I

variable {I}

/--
theorem `mul_mono` / 定理 `mul_mono`

English:
theorem mul_mono
  given: (hik : I <= K) (hjl : J <= L)
  statement: I * J <= K * L
  proof: Submodule.smul_mono hik hjl

中文:
定理 mul_mono
  条件: (hik : I <= K) (hjl : J <= L)
  结论: I * J <= K * L
  证明: Submodule.smul_mono hik hjl

Depends on / 依赖: Submodule, Submodule.smul_mono, smul_mono
-/
theorem mul_mono (hik : I <= K) (hjl : J <= L) : I * J <= K * L :=
  Submodule.smul_mono hik hjl

/--
theorem `mul_mono_left` / 定理 `mul_mono_left`

English:
theorem mul_mono_left
  given: (h : I <= J)
  statement: I * K <= J * K
  proof: Submodule.smul_mono_left h

中文:
定理 mul_mono_left
  条件: (h : I <= J)
  结论: I * K <= J * K
  证明: Submodule.smul_mono_left h

Depends on / 依赖: Submodule, Submodule.smul_mono_left, smul_mono_left
-/
theorem mul_mono_left (h : I <= J) : I * K <= J * K :=
  Submodule.smul_mono_left h

/--
theorem `mul_mono_right` / 定理 `mul_mono_right`

English:
theorem mul_mono_right
  given: (h : J <= K)
  statement: I * J <= I * K
  proof: smul_mono_right I h

中文:
定理 mul_mono_right
  条件: (h : J <= K)
  结论: I * J <= I * K
  证明: smul_mono_right I h

Depends on / 依赖: smul_mono_right
-/
theorem mul_mono_right (h : J <= K) : I * J <= I * K :=
  smul_mono_right I h

variable (I J K)

/--
theorem `mul_sup` / 定理 `mul_sup`

English:
theorem mul_sup
  statement: I * (J ⊔ K) = I * J ⊔ I * K
  proof: Submodule.smul_sup I J K

中文:
定理 mul_sup
  结论: I * (J ⊔ K) = I * J ⊔ I * K
  证明: Submodule.smul_sup I J K

Depends on / 依赖: Submodule, Submodule.smul_sup, smul_sup
-/
theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
  Submodule.smul_sup I J K

/--
theorem `sup_mul` / 定理 `sup_mul`

English:
theorem sup_mul
  statement: (I ⊔ J) * K = I * K ⊔ J * K
  proof: Submodule.sup_smul I J K

中文:
定理 sup_mul
  结论: (I ⊔ J) * K = I * K ⊔ J * K
  证明: Submodule.sup_smul I J K

Depends on / 依赖: Submodule, Submodule.sup_smul, sup_smul
-/
theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
  Submodule.sup_smul I J K

/--
theorem `mul_iSup` / 定理 `mul_iSup`

English:
theorem mul_iSup
  given: {ι : Sort*} (J : ι -> Ideal R)
  proof: Submodule.smul_iSup

中文:
定理 mul_iSup
  条件: {ι : 类型层*} (J : ι -> 理想 R)
  证明: Submodule.smul_iSup

Depends on / 依赖: Submodule, Submodule.smul_iSup, smul_iSup
-/
theorem mul_iSup {ι : Sort*} (J : ι -> Ideal R) :
    I * (⨆ i, J i) = ⨆ i, I * J i :=
  Submodule.smul_iSup

/--
theorem `iSup_mul` / 定理 `iSup_mul`

English:
theorem iSup_mul
  given: {ι : Sort*} (J : ι -> Ideal R) (I : Ideal R)
  proof: Submodule.iSup_smul

中文:
定理 iSup_mul
  条件: {ι : 类型层*} (J : ι -> 理想 R) (I : 理想 R)
  证明: Submodule.iSup_smul

Depends on / 依赖: Submodule, Submodule.iSup_smul, iSup_smul
-/
theorem iSup_mul {ι : Sort*} (J : ι -> Ideal R) (I : Ideal R) :
    (⨆ i, J i) * I = ⨆ i, J i * I :=
  Submodule.iSup_smul

variable {I J K}

/--
theorem `pow_le_pow_right` / 定理 `pow_le_pow_right`

English:
theorem pow_le_pow_right
  given: {m n : Nat} (h : m <= n)
  statement: I ^ n <= I ^ m
  proof: by
  obtain _ | m := m
  · rw [Submodule.pow_zero, one_eq_top]; exact le_top
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]; rw [Submodule.pow_add _ m.add_one_ne_zero]
  exact mul_le_right

中文:
定理 pow_le_pow_right
  条件: {m n : 自然数} (h : m <= n)
  结论: I ^ n <= I ^ m
  证明: by
  obtain _ | m := m
  · rw [Submodule.pow_zero, one_eq_top]; exact le_top
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]; rw [Submodule.pow_add _ m.add_one_ne_zero]
  exact mul_le_right

Depends on / 依赖: Nat.exists_eq_add_of_le, Submodule, Submodule.pow_add, Submodule.pow_zero, add_comm, add_one_ne_zero, exists_eq_add_of_le, le_top, m.add_one_ne_zero, mul_le_right, one_eq_top, pow_add, pow_zero
-/
theorem pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ n <= I ^ m := by
  obtain _ | m := m
  · rw [Submodule.pow_zero, one_eq_top]; exact le_top
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]; rw [Submodule.pow_add _ m.add_one_ne_zero]
  exact mul_le_right

/--
theorem `pow_le_self` / 定理 `pow_le_self`

English:
theorem pow_le_self
  given: {n : Nat} (hn : n != 0)
  statement: I ^ n <= I
  proof: calc
    I ^ n <= I ^ 1 := pow_le_pow_right (Nat.pos_of_ne_zero hn)
    _ = I := Submodule.pow_one _

中文:
定理 pow_le_self
  条件: {n : 自然数} (hn : n != 0)
  结论: I ^ n <= I
  证明: calc
    I ^ n <= I ^ 1 := pow_le_pow_right (Nat.pos_of_ne_zero hn)
    _ = I := Submodule.pow_one _

Depends on / 依赖: Nat.pos_of_ne_zero, Submodule, Submodule.pow_one, pos_of_ne_zero, pow_le_pow_right, pow_one
-/
theorem pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I :=
  calc
    I ^ n <= I ^ 1 := pow_le_pow_right (Nat.pos_of_ne_zero hn)
    _ = I := Submodule.pow_one _

/--
theorem `pow_right_mono` / 定理 `pow_right_mono`

English:
theorem pow_right_mono
  given: (e : I <= J) (n : Nat)
  statement: I ^ n <= J ^ n
  proof: by
  induction n with
  | zero => rw [Submodule.pow_zero, Submodule.pow_zero]
  | succ _ hn =>
    rw [Submodule.pow_succ]; rw [Submodule.pow_succ]
    exact Ideal.mul_mono hn e

中文:
定理 pow_right_mono
  条件: (e : I <= J) (n : 自然数)
  结论: I ^ n <= J ^ n
  证明: by
  induction n with
  | zero => rw [Submodule.pow_zero, Submodule.pow_zero]
  | succ _ hn =>
    rw [Submodule.pow_succ]; rw [Submodule.pow_succ]
    exact Ideal.mul_mono hn e

Depends on / 依赖: Ideal.mul_mono, Submodule, Submodule.pow_succ, Submodule.pow_zero, mul_mono, pow_succ, pow_zero
-/
theorem pow_right_mono (e : I <= J) (n : Nat) : I ^ n <= J ^ n := by
  induction n with
  | zero => rw [Submodule.pow_zero, Submodule.pow_zero]
  | succ _ hn =>
    rw [Submodule.pow_succ]; rw [Submodule.pow_succ]
    exact Ideal.mul_mono hn e

namespace IsTwoSided

instance (priority := low) [J.IsTwoSided] : (I * J).IsTwoSided :=
  ⟨fun b ha => Submodule.mul_induction_on ha
    (fun i hi j hj => by rw [mul_assoc]; exact mul_mem_mul hi (mul_mem_right _ _ hj))
    fun x y hx hy => by rw [right_distrib]; exact add_mem hx hy⟩

variable [I.IsTwoSided] (m n : Nat)

instance (priority := low) : (I ^ n).IsTwoSided :=
  n.rec
    (by rw [Submodule.pow_zero, one_eq_top]; infer_instance)
    (fun _ _ => by rw [Submodule.pow_succ]; infer_instance)

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  statement: I * 1 = I
  proof: mul_le_left.antisymm
    fun i hi => mul_one i ▸ mul_mem_mul hi (one_eq_top (R := R) ▸ Submodule.mem_top)

中文:
定理 mul_one
  结论: I * 1 = I
  证明: mul_le_left.antisymm
    fun i hi => mul_one i ▸ mul_mem_mul hi (one_eq_top (R := R) ▸ Submodule.mem_top)
-/
protected theorem mul_one : I * 1 = I :=
  mul_le_left.antisymm
    fun i hi => mul_one i ▸ mul_mem_mul hi (one_eq_top (R := R) ▸ Submodule.mem_top)

/--
theorem `pow_add` / 定理 `pow_add`

English:
theorem pow_add
  statement: I ^ (m + n) = I ^ m * I ^ n
  proof: by
  obtain rfl | h := eq_or_ne n 0
  · rw [add_zero, Submodule.pow_zero, IsTwoSided.mul_one]
  · exact Submodule.pow_add _ h

中文:
定理 pow_add
  结论: I ^ (m + n) = I ^ m * I ^ n
  证明: by
  obtain rfl | h := eq_or_ne n 0
  · rw [add_zero, Submodule.pow_zero, IsTwoSided.mul_one]
  · exact Submodule.pow_add _ h
-/
protected theorem pow_add : I ^ (m + n) = I ^ m * I ^ n := by
  obtain rfl | h := eq_or_ne n 0
  · rw [add_zero, Submodule.pow_zero, IsTwoSided.mul_one]
  · exact Submodule.pow_add _ h

/--
theorem `pow_succ` / 定理 `pow_succ`

English:
theorem pow_succ
  statement: I ^ (n + 1) = I * I ^ n
  proof: by
  rw [add_comm]; rw [IsTwoSided.pow_add]; rw [Submodule.pow_one]

中文:
定理 pow_succ
  结论: I ^ (n + 1) = I * I ^ n
  证明: by
  rw [add_comm]; rw [IsTwoSided.pow_add]; rw [Submodule.pow_one]
-/
protected theorem pow_succ : I ^ (n + 1) = I * I ^ n := by
  rw [add_comm]; rw [IsTwoSided.pow_add]; rw [Submodule.pow_one]

end IsTwoSided

/--
theorem `mul_eq_bot` / 定理 `mul_eq_bot`

English:
theorem mul_eq_bot
  given: [NoZeroDivisors R]
  statement: I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥
  proof: Submodule.mul_eq_bot

中文:
定理 mul_eq_bot
  条件: [无零因子 R]
  结论: I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥
  证明: Submodule.mul_eq_bot

Depends on / 依赖: Submodule, Submodule.mul_eq_bot, mul_eq_bot
-/
theorem mul_eq_bot [NoZeroDivisors R] : I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ := Submodule.mul_eq_bot

/--
theorem `pow_eq_bot` / 定理 `pow_eq_bot`

English:
theorem pow_eq_bot
  given: [IsReduced R] {n : Nat} (hn : n != 0)
  statement: I ^ n = ⊥ ↔ I = ⊥
  proof: Submodule.pow_eq_bot hn

中文:
定理 pow_eq_bot
  条件: [是既约 R] {n : 自然数} (hn : n != 0)
  结论: I ^ n = ⊥ ↔ I = ⊥
  证明: Submodule.pow_eq_bot hn

Depends on / 依赖: Submodule, Submodule.pow_eq_bot, pow_eq_bot
-/
theorem pow_eq_bot [IsReduced R] {n : Nat} (hn : n != 0) : I ^ n = ⊥ ↔ I = ⊥ :=
  Submodule.pow_eq_bot hn

instance {S A : Type*} [Semiring S] [SMul R S] [AddCommMonoid A] [Module R A] [Module S A]
    [IsScalarTower R S A] [IsTorsionFree R A] {I : Submodule S A} : IsTorsionFree R I :=
  (I.restrictScalars R).instIsTorsionFree

/--
theorem `span_mul_span` / 定理 `span_mul_span`

English:
theorem span_mul_span
  given: (S T : Set R) [(span S).IsTwoSided]
  proof: Submodule.span_smul_span S T

中文:
定理 span_mul_span
  条件: (S T : 集合 R) [(span S).是TwoSided]
  证明: Submodule.span_smul_span S T

Depends on / 依赖: Submodule, Submodule.span_smul_span, span_smul_span
-/
theorem span_mul_span (S T : Set R) [(span S).IsTwoSided] :
    span S * span T = span (S * T) :=
  Submodule.span_smul_span S T

/--
theorem `span_mul_span'` / 定理 `span_mul_span'`

English:
theorem span_mul_span'
  given: (S T : Set R) [(span S).IsTwoSided]
  statement: span S * span T = span (S * T)
  proof: (span_mul_span S T).trans congr_arg span Set.ext by simp [Set.mem_mul, eq_comm]

中文:
定理 span_mul_span'
  条件: (S T : 集合 R) [(span S).是TwoSided]
  结论: span S * span T = span (S * T)
  证明: (span_mul_span S T).trans congr_arg span Set.ext by simp [Set.mem_mul, eq_comm]

Depends on / 依赖: Set.ext, Set.mem_mul, congr_arg, eq_comm, mem_mul, span_mul_span
-/
theorem span_mul_span' (S T : Set R) [(span S).IsTwoSided] : span S * span T = span (S * T) :=
(span_mul_span S T).trans congr_arg span Set.ext by simp [Set.mem_mul, eq_comm]

/--
theorem `span_singleton_mul_span_singleton` / 定理 `span_singleton_mul_span_singleton`

English:
theorem span_singleton_mul_span_singleton
  given: (r s : R) [(span {r}).IsTwoSided]
  proof: by
  rw [span_mul_span']; rw [Set.singleton_mul_singleton]

中文:
定理 span_singleton_mul_span_singleton
  条件: (r s : R) [(span {r}).是TwoSided]
  证明: by
  rw [span_mul_span']; rw [Set.singleton_mul_singleton]

Depends on / 依赖: Set.singleton_mul_singleton, singleton_mul_singleton, span_mul_span
-/
theorem span_singleton_mul_span_singleton (r s : R) [(span {r}).IsTwoSided] :
    span {r} * span {s} = (span {r * s} : Ideal R) := by
  rw [span_mul_span']; rw [Set.singleton_mul_singleton]

/--
theorem `span_singleton_pow` / 定理 `span_singleton_pow`

English:
theorem span_singleton_pow
  given: (s : R) [(span {s}).IsTwoSided] (n : Nat)
  proof: by
  induction n with
  | zero => simp [Submodule.pow_zero, Set.singleton_one]
  | succ n ih =>
    obtain rfl | ne := eq_or_ne n 0; · simp [Submodule.pow_one]
    simp only [Submodule.pow_succ' _ ne, pow_succ', ih, span_singleton_mul_span_singleton]

中文:
定理 span_singleton_pow
  条件: (s : R) [(span {s}).是TwoSided] (n : 自然数)
  证明: by
  induction n with
  | zero => simp [Submodule.pow_zero, Set.singleton_one]
  | succ n ih =>
    obtain rfl | ne := eq_or_ne n 0; · simp [Submodule.pow_one]
    simp only [Submodule.pow_succ' _ ne, pow_succ', ih, span_singleton_mul_span_singleton]

Depends on / 依赖: Set.singleton_one, Submodule, Submodule.pow_one, Submodule.pow_succ, Submodule.pow_zero, eq_or_ne, pow_one, pow_succ, pow_zero, singleton_one, span_singleton_mul_span_singleton
-/
theorem span_singleton_pow (s : R) [(span {s}).IsTwoSided] (n : Nat) :
    span {s} ^ n = (span {s ^ n} : Ideal R) := by
  induction n with
  | zero => simp [Submodule.pow_zero, Set.singleton_one]
  | succ n ih =>
    obtain rfl | ne := eq_or_ne n 0; · simp [Submodule.pow_one]
    simp only [Submodule.pow_succ' _ ne, pow_succ', ih, span_singleton_mul_span_singleton]

/--
theorem `mem_mul_span_singleton` / 定理 `mem_mul_span_singleton`

English:
theorem mem_mul_span_singleton
  given: {x y : R} {I : Ideal R} [I.IsTwoSided]
  proof: Submodule.mem_smul_span_singleton

中文:
定理 mem_mul_span_singleton
  条件: {x y : R} {I : 理想 R} [I.是TwoSided]
  证明: Submodule.mem_smul_span_singleton

Depends on / 依赖: Submodule, Submodule.mem_smul_span_singleton, mem_smul_span_singleton
-/
theorem mem_mul_span_singleton {x y : R} {I : Ideal R} [I.IsTwoSided] :
    x in I * span {y} ↔ exists z in I, z * y = x :=
  Submodule.mem_smul_span_singleton

/--
theorem `span_singleton_mul_left_mono` / 定理 `span_singleton_mul_left_mono`

English:
theorem span_singleton_mul_left_mono
  statement: [IsDomain R] [I.IsTwoSided] [J.IsTwoSided]
  proof: by
  simp [SetLike.le_def, mem_mul_span_singleton, hx]

中文:
定理 span_singleton_mul_left_mono
  结论: [是整环 R] [I.是TwoSided] [J.是TwoSided]
  证明: by
  simp [SetLike.le_def, mem_mul_span_singleton, hx]

Depends on / 依赖: SetLike, SetLike.le_def, le_def, mem_mul_span_singleton
-/
theorem span_singleton_mul_left_mono [IsDomain R] [I.IsTwoSided] [J.IsTwoSided]
    {x : R} (hx : x != 0) : I * span {x} <= J * span {x} ↔ I <= J := by
  simp [SetLike.le_def, mem_mul_span_singleton, hx]

/--
theorem `span_singleton_mul_left_inj` / 定理 `span_singleton_mul_left_inj`

English:
theorem span_singleton_mul_left_inj
  statement: [IsDomain R] [I.IsTwoSided] [J.IsTwoSided]
  proof: by
  simp only [le_antisymm_iff, span_singleton_mul_left_mono hx]

中文:
定理 span_singleton_mul_left_inj
  结论: [是整环 R] [I.是TwoSided] [J.是TwoSided]
  证明: by
  simp only [le_antisymm_iff, span_singleton_mul_left_mono hx]

Depends on / 依赖: le_antisymm_iff, span_singleton_mul_left_mono
-/
theorem span_singleton_mul_left_inj [IsDomain R] [I.IsTwoSided] [J.IsTwoSided]
    {x : R} (hx : x != 0) : I * span {x} = J * span {x} ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_left_mono hx]

/--
theorem `mul_le_inf` / 定理 `mul_le_inf`

English:
theorem mul_le_inf
  given: [I.IsTwoSided]
  statement: I * J <= I ⊓ J
  proof: mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

中文:
定理 mul_le_inf
  条件: [I.是TwoSided]
  结论: I * J <= I ⊓ J
  证明: mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

Depends on / 依赖: I.mul_mem_right, J.mul_mem_left, mul_le, mul_mem_left, mul_mem_right
-/
theorem mul_le_inf [I.IsTwoSided] : I * J <= I ⊓ J :=
  mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

/--
lemma `inf_ne_bot_of_ne_bot` / 引理 `inf_ne_bot_of_ne_bot`

English:
lemma inf_ne_bot_of_ne_bot
  statement: [NoZeroDivisors R] {I J : Ideal R} [I.IsTwoSided]
  proof: by
  grw [← bot_lt_iff_ne_bot, ← mul_le_inf, bot_lt_iff_ne_bot, Ne, mul_eq_bot]
  exact not_or_intro hI hJ

中文:
引理 inf_ne_bot_of_ne_bot
  结论: [无零因子 R] {I J : 理想 R} [I.是TwoSided]
  证明: by
  grw [← bot_lt_iff_ne_bot, ← mul_le_inf, bot_lt_iff_ne_bot, Ne, mul_eq_bot]
  exact not_or_intro hI hJ

Depends on / 依赖: bot_lt_iff_ne_bot, mul_eq_bot, mul_le_inf, not_or_intro
-/
lemma inf_ne_bot_of_ne_bot [NoZeroDivisors R] {I J : Ideal R} [I.IsTwoSided]
    (hI : I != ⊥) (hJ : J != ⊥) :
    I ⊓ J != ⊥ := by
  grw [← bot_lt_iff_ne_bot, ← mul_le_inf, bot_lt_iff_ne_bot, Ne, mul_eq_bot]
  exact not_or_intro hI hJ

/--
theorem `sup_mul_eq_of_coprime_left` / 定理 `sup_mul_eq_of_coprime_left`

English:
theorem sup_mul_eq_of_coprime_left
  given: [I.IsTwoSided] (h : I ⊔ J = ⊤)
  statement: I ⊔ J * K = I ⊔ K
  proof: le_antisymm (sup_le_sup_left mul_le_right _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h; obtain ⟨i', hi', k, hk, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← a

中文:
定理 sup_mul_eq_of_coprime_left
  条件: [I.是TwoSided] (h : I ⊔ J = ⊤)
  结论: I ⊔ J * K = I ⊔ K
  证明: le_antisymm (sup_le_sup_left mul_le_right _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h; obtain ⟨i', hi', k, hk, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← a

Depends on / 依赖: Submodule, Submodule.mem_sup, add_assoc, add_mem, add_mul, eq_top_iff_one, le_antisymm, mem_sup, mul_le_right, mul_mem_mul, mul_mem_right, one_mul, sup_le_sup_left
-/
theorem sup_mul_eq_of_coprime_left [I.IsTwoSided] (h : I ⊔ J = ⊤) : I ⊔ J * K = I ⊔ K :=
  le_antisymm (sup_le_sup_left mul_le_right _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h; obtain ⟨i', hi', k, hk, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← add_mul]; rw [h]; rw [one_mul]

/--
theorem `sup_mul_eq_of_coprime_right` / 定理 `sup_mul_eq_of_coprime_right`

English:
theorem sup_mul_eq_of_coprime_right
  given: [J.IsTwoSided] (h : I ⊔ K = ⊤)
  statement: I ⊔ J * K = I ⊔ J
  proof: le_antisymm (sup_le_sup_left mul_le_left _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, k, hk, h⟩ := h; obtain ⟨i', hi', j, hj, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_left _ j hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← mul

中文:
定理 sup_mul_eq_of_coprime_right
  条件: [J.是TwoSided] (h : I ⊔ K = ⊤)
  结论: I ⊔ J * K = I ⊔ J
  证明: le_antisymm (sup_le_sup_left mul_le_left _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, k, hk, h⟩ := h; obtain ⟨i', hi', j, hj, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_left _ j hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← mul

Depends on / 依赖: Submodule, Submodule.mem_sup, add_assoc, add_mem, eq_top_iff_one, le_antisymm, mem_sup, mul_add, mul_le_left, mul_mem_left, mul_mem_mul, mul_one, sup_le_sup_left
-/
theorem sup_mul_eq_of_coprime_right [J.IsTwoSided] (h : I ⊔ K = ⊤) : I ⊔ J * K = I ⊔ J :=
  le_antisymm (sup_le_sup_left mul_le_left _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, k, hk, h⟩ := h; obtain ⟨i', hi', j, hj, rfl⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_left _ j hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc]; rw [← mul_add]; rw [h]; rw [mul_one]

/--
theorem `mul_sup_eq_of_coprime_left` / 定理 `mul_sup_eq_of_coprime_left`

English:
theorem mul_sup_eq_of_coprime_left
  given: [J.IsTwoSided] (h : I ⊔ J = ⊤)
  statement: I * K ⊔ J = K ⊔ J
  proof: by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_left h]; rw [sup_comm]

中文:
定理 mul_sup_eq_of_coprime_left
  条件: [J.是TwoSided] (h : I ⊔ J = ⊤)
  结论: I * K ⊔ J = K ⊔ J
  证明: by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_left h]; rw [sup_comm]

Depends on / 依赖: sup_comm, sup_mul_eq_of_coprime_left
-/
theorem mul_sup_eq_of_coprime_left [J.IsTwoSided] (h : I ⊔ J = ⊤) : I * K ⊔ J = K ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_left h]; rw [sup_comm]

/--
theorem `mul_sup_eq_of_coprime_right` / 定理 `mul_sup_eq_of_coprime_right`

English:
theorem mul_sup_eq_of_coprime_right
  given: [I.IsTwoSided] (h : K ⊔ J = ⊤)
  statement: I * K ⊔ J = I ⊔ J
  proof: by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_right h]; rw [sup_comm]

中文:
定理 mul_sup_eq_of_coprime_right
  条件: [I.是TwoSided] (h : K ⊔ J = ⊤)
  结论: I * K ⊔ J = I ⊔ J
  证明: by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_right h]; rw [sup_comm]

Depends on / 依赖: sup_comm, sup_mul_eq_of_coprime_right
-/
theorem mul_sup_eq_of_coprime_right [I.IsTwoSided] (h : K ⊔ J = ⊤) : I * K ⊔ J = I ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm]; rw [sup_mul_eq_of_coprime_right h]; rw [sup_comm]

variable {ι : Type*}

/--
theorem `sup_iInf_eq_top` / 定理 `sup_iInf_eq_top`

English:
theorem sup_iInf_eq_top
  statement: {s : Finset ι} {J : ι -> Ideal R} [forall i, (J i).IsTwoSided]
  proof: by
  classical
exact s.induction_on' (by simp) fun {i t} his hts hit eq_top => top_unique by
    rw [Finset.iInf_insert]; rw [inf_comm]
    refine le_trans ?_ (sup_le_sup_left mul_le_inf _)
    simpa only [sup_mul_eq_of_coprime_right (h _ his)] using eq_top.ge

中文:
定理 sup_iInf_eq_top
  结论: {s : 有限集 ι} {J : ι -> 理想 R} [对任意 i, (J i).是TwoSided]
  证明: by
  classical
exact s.induction_on' (by simp) fun {i t} his hts hit eq_top => top_unique by
    rw [Finset.iInf_insert]; rw [inf_comm]
    refine le_trans ?_ (sup_le_sup_left mul_le_inf _)
    simpa only [sup_mul_eq_of_coprime_right (h _ his)] using eq_top.ge

Depends on / 依赖: Finset, Finset.iInf_insert, classical, eq_top, eq_top.ge, iInf_insert, induction_on, inf_comm, le_trans, mul_le_inf, s.induction_on, sup_le_sup_left, sup_mul_eq_of_coprime_right, top_unique
-/
theorem sup_iInf_eq_top {s : Finset ι} {J : ι -> Ideal R} [forall i, (J i).IsTwoSided]
    (h : forall i, i in s -> I ⊔ J i = ⊤) : (I ⊔ ⨅ i in s, J i) = ⊤ := by
  classical
exact s.induction_on' (by simp) fun {i t} his hts hit eq_top => top_unique by
    rw [Finset.iInf_insert]; rw [inf_comm]
    refine le_trans ?_ (sup_le_sup_left mul_le_inf _)
    simpa only [sup_mul_eq_of_coprime_right (h _ his)] using eq_top.ge

/--
theorem `iInf_sup_eq_top` / 定理 `iInf_sup_eq_top`

English:
theorem iInf_sup_eq_top
  statement: {s : Finset ι} {J : ι -> Ideal R} [forall i, (J i).IsTwoSided]
  proof: by
  rw [sup_comm]; rw [sup_iInf_eq_top]; intro i hi; rw [sup_comm, h i hi]

中文:
定理 iInf_sup_eq_top
  结论: {s : 有限集 ι} {J : ι -> 理想 R} [对任意 i, (J i).是TwoSided]
  证明: by
  rw [sup_comm]; rw [sup_iInf_eq_top]; intro i hi; rw [sup_comm, h i hi]

Depends on / 依赖: sup_comm, sup_iInf_eq_top
-/
theorem iInf_sup_eq_top {s : Finset ι} {J : ι -> Ideal R} [forall i, (J i).IsTwoSided]
    (h : forall i, i in s -> J i ⊔ I = ⊤) : (⨅ i in s, J i) ⊔ I = ⊤ := by
  rw [sup_comm]; rw [sup_iInf_eq_top]; intro i hi; rw [sup_comm, h i hi]

/--
theorem `sup_pow_eq_top` / 定理 `sup_pow_eq_top`

English:
theorem sup_pow_eq_top
  given: [I.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤)
  statement: I ⊔ J ^ n = ⊤
  proof: by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih => rwa [J.pow_succ, sup_mul_eq_of_coprime_left ih]

中文:
定理 sup_pow_eq_top
  条件: [I.是TwoSided] {n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ⊔ J ^ n = ⊤
  证明: by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih => rwa [J.pow_succ, sup_mul_eq_of_coprime_left ih]

Depends on / 依赖: J.pow_succ, J.pow_zero, pow_succ, pow_zero, sup_mul_eq_of_coprime_left
-/
theorem sup_pow_eq_top [I.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ := by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih => rwa [J.pow_succ, sup_mul_eq_of_coprime_left ih]

/--
theorem `sup_pow_eq_top'` / 定理 `sup_pow_eq_top'`

English:
theorem sup_pow_eq_top'
  given: [J.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤)
  statement: I ⊔ J ^ n = ⊤
  proof: by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih =>
    obtain rfl | hn := eq_or_ne n 0; · simpa [J.pow_one] using h
    rwa [J.pow_succ' hn, sup_mul_eq_of_coprime_right ih]

中文:
定理 sup_pow_eq_top'
  条件: [J.是TwoSided] {n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ⊔ J ^ n = ⊤
  证明: by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih =>
    obtain rfl | hn := eq_or_ne n 0; · simpa [J.pow_one] using h
    rwa [J.pow_succ' hn, sup_mul_eq_of_coprime_right ih]

Depends on / 依赖: J.pow_one, J.pow_succ, J.pow_zero, eq_or_ne, pow_one, pow_succ, pow_zero, sup_mul_eq_of_coprime_right
-/
theorem sup_pow_eq_top' [J.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ := by
  induction n with
  | zero => simp [J.pow_zero]
  | succ n ih =>
    obtain rfl | hn := eq_or_ne n 0; · simpa [J.pow_one] using h
    rwa [J.pow_succ' hn, sup_mul_eq_of_coprime_right ih]

/--
theorem `pow_sup_eq_top` / 定理 `pow_sup_eq_top`

English:
theorem pow_sup_eq_top
  given: [I.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤)
  statement: I ^ n ⊔ J = ⊤
  proof: by
  rw [sup_comm]; rw [sup_pow_eq_top' (sup_comm I J ▸ h)]

中文:
定理 pow_sup_eq_top
  条件: [I.是TwoSided] {n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ^ n ⊔ J = ⊤
  证明: by
  rw [sup_comm]; rw [sup_pow_eq_top' (sup_comm I J ▸ h)]

Depends on / 依赖: sup_comm, sup_pow_eq_top
-/
theorem pow_sup_eq_top [I.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤) : I ^ n ⊔ J = ⊤ := by
  rw [sup_comm]; rw [sup_pow_eq_top' (sup_comm I J ▸ h)]

/--
theorem `pow_sup_eq_top'` / 定理 `pow_sup_eq_top'`

English:
theorem pow_sup_eq_top'
  given: [J.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤)
  statement: I ^ n ⊔ J = ⊤
  proof: by
  rw [sup_comm]; rw [sup_pow_eq_top (sup_comm I J ▸ h)]

中文:
定理 pow_sup_eq_top'
  条件: [J.是TwoSided] {n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ^ n ⊔ J = ⊤
  证明: by
  rw [sup_comm]; rw [sup_pow_eq_top (sup_comm I J ▸ h)]

Depends on / 依赖: sup_comm, sup_pow_eq_top
-/
theorem pow_sup_eq_top' [J.IsTwoSided] {n : Nat} (h : I ⊔ J = ⊤) : I ^ n ⊔ J = ⊤ := by
  rw [sup_comm]; rw [sup_pow_eq_top (sup_comm I J ▸ h)]

/--
theorem `pow_sup_pow_eq_top` / 定理 `pow_sup_pow_eq_top`

English:
theorem pow_sup_pow_eq_top
  given: [I.IsTwoSided] {m n : Nat} (h : I ⊔ J = ⊤)
  statement: I ^ m ⊔ J ^ n = ⊤
  proof: pow_sup_eq_top (sup_pow_eq_top h)

中文:
定理 pow_sup_pow_eq_top
  条件: [I.是TwoSided] {m n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ^ m ⊔ J ^ n = ⊤
  证明: pow_sup_eq_top (sup_pow_eq_top h)

Depends on / 依赖: pow_sup_eq_top, sup_pow_eq_top
-/
theorem pow_sup_pow_eq_top [I.IsTwoSided] {m n : Nat} (h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤ :=
  pow_sup_eq_top (sup_pow_eq_top h)

/--
theorem `pow_sup_pow_eq_top'` / 定理 `pow_sup_pow_eq_top'`

English:
theorem pow_sup_pow_eq_top'
  given: [J.IsTwoSided] {m n : Nat} (h : I ⊔ J = ⊤)
  statement: I ^ m ⊔ J ^ n = ⊤
  proof: pow_sup_eq_top' (sup_pow_eq_top' h)

中文:
定理 pow_sup_pow_eq_top'
  条件: [J.是TwoSided] {m n : 自然数} (h : I ⊔ J = ⊤)
  结论: I ^ m ⊔ J ^ n = ⊤
  证明: pow_sup_eq_top' (sup_pow_eq_top' h)

Depends on / 依赖: pow_sup_eq_top, sup_pow_eq_top
-/
theorem pow_sup_pow_eq_top' [J.IsTwoSided] {m n : Nat} (h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤ :=
  pow_sup_eq_top' (sup_pow_eq_top' h)

variable (I) in
@[simp]
/--
theorem `mul_top` / 定理 `mul_top`

English:
theorem mul_top
  given: [I.IsTwoSided]
  statement: I * ⊤ = I
  proof: le_antisymm (mul_le.mpr fun _i hi _r _ => mul_mem_right _ _ hi)
    fun i hi => mul_one i ▸ mul_mem_mul hi Submodule.mem_top

中文:
定理 mul_top
  条件: [I.是TwoSided]
  结论: I * ⊤ = I
  证明: le_antisymm (mul_le.mpr fun _i hi _r _ => mul_mem_right _ _ hi)
    fun i hi => mul_one i ▸ mul_mem_mul hi Submodule.mem_top

Depends on / 依赖: Submodule, Submodule.mem_top, le_antisymm, mem_top, mul_le, mul_le.mpr, mul_mem_mul, mul_mem_right, mul_one
-/
theorem mul_top [I.IsTwoSided] : I * ⊤ = I :=
  le_antisymm (mul_le.mpr fun _i hi _r _ => mul_mem_right _ _ hi)
    fun i hi => mul_one i ▸ mul_mem_mul hi Submodule.mem_top

/--
theorem `span_pair_mul_span_pair` / 定理 `span_pair_mul_span_pair`

English:
theorem span_pair_mul_span_pair
  given: (w x y z : R) [(span {w, x}).IsTwoSided]
  proof: by
  rw [span_mul_span']; congr; ext r; simp [Set.mem_mul, or_assoc, eq_comm (a := r)]

中文:
定理 span_pair_mul_span_pair
  条件: (w x y z : R) [(span {w, x}).是TwoSided]
  证明: by
  rw [span_mul_span']; congr; ext r; simp [Set.mem_mul, or_assoc, eq_comm (a := r)]

Depends on / 依赖: Set.mem_mul, eq_comm, mem_mul, or_assoc, span_mul_span
-/
theorem span_pair_mul_span_pair (w x y z : R) [(span {w, x}).IsTwoSided] :
    (span {w, x} : Ideal R) * span {y, z} = span {w * y, w * z, x * y, x * z} := by
  rw [span_mul_span']; congr; ext r; simp [Set.mem_mul, or_assoc, eq_comm (a := r)]

variable (R) in
/--
theorem `top_pow` / 定理 `top_pow`

English:
theorem top_pow
  given: (n : Nat)
  statement: (⊤ ^ n : Ideal R) = ⊤
  proof: Nat.recOn n one_eq_top fun n ih => by rw [Submodule.pow_succ, ih, top_mul]

@[simp]

中文:
定理 top_pow
  条件: (n : 自然数)
  结论: (⊤ ^ n : 理想 R) = ⊤
  证明: Nat.recOn n one_eq_top fun n ih => by rw [Submodule.pow_succ, ih, top_mul]

@[simp]

Depends on / 依赖: Nat.recOn, Submodule, Submodule.pow_succ, one_eq_top, pow_succ, top_mul
-/
theorem top_pow (n : Nat) : (⊤ ^ n : Ideal R) = ⊤ :=
  Nat.recOn n one_eq_top fun n ih => by rw [Submodule.pow_succ, ih, top_mul]

@[simp]
/--
theorem `pow_eq_top_iff` / 定理 `pow_eq_top_iff`

English:
theorem pow_eq_top_iff
  given: {n : Nat}
  proof: by
  refine ⟨fun h => or_iff_not_imp_right.mpr
fun hn => (eq_top_iff_one _).mpr pow_le_self hn (eq_top_iff_one _).mp h, ?_⟩
  rintro (h | h)
  · rw [h, top_pow]
  · rw [h, Submodule.pow_zero, one_eq_top]

中文:
定理 pow_eq_top_iff
  条件: {n : 自然数}
  证明: by
  refine ⟨fun h => or_iff_not_imp_right.mpr
fun hn => (eq_top_iff_one _).mpr pow_le_self hn (eq_top_iff_one _).mp h, ?_⟩
  rintro (h | h)
  · rw [h, top_pow]
  · rw [h, Submodule.pow_zero, one_eq_top]

Depends on / 依赖: Submodule, Submodule.pow_zero, eq_top_iff_one, one_eq_top, or_iff_not_imp_right, or_iff_not_imp_right.mpr, pow_le_self, pow_zero, top_pow
-/
theorem pow_eq_top_iff {n : Nat} :
    I ^ n = ⊤ ↔ I = ⊤ ∨ n = 0 := by
  refine ⟨fun h => or_iff_not_imp_right.mpr
fun hn => (eq_top_iff_one _).mpr pow_le_self hn (eq_top_iff_one _).mp h, ?_⟩
  rintro (h | h)
  · rw [h, top_pow]
  · rw [h, Submodule.pow_zero, one_eq_top]

/--
theorem `natCast_eq_top` / 定理 `natCast_eq_top`

English:
theorem natCast_eq_top
  given: {n : Nat} (hn : n != 0)
  statement: (n : Ideal R) = ⊤
  proof: by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    obtain rfl | n := n; · rw [Nat.cast_one, one_eq_top]
    rw [Nat.cast_succ]; rw [ih n.succ_ne_zero]; rw [add_eq_sup]; rw [top_sup_eq]

中文:
定理 natCast_eq_top
  条件: {n : 自然数} (hn : n != 0)
  结论: (n : 理想 R) = ⊤
  证明: by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    obtain rfl | n := n; · rw [Nat.cast_one, one_eq_top]
    rw [Nat.cast_succ]; rw [ih n.succ_ne_zero]; rw [add_eq_sup]; rw [top_sup_eq]

Depends on / 依赖: Nat.cast_one, Nat.cast_succ, add_eq_sup, cast_one, cast_succ, n.succ_ne_zero, one_eq_top, succ_ne_zero, top_sup_eq
-/
theorem natCast_eq_top {n : Nat} (hn : n != 0) : (n : Ideal R) = ⊤ := by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    obtain rfl | n := n; · rw [Nat.cast_one, one_eq_top]
    rw [Nat.cast_succ]; rw [ih n.succ_ne_zero]; rw [add_eq_sup]; rw [top_sup_eq]

/--
theorem `ofNat_eq_top` / 定理 `ofNat_eq_top`

English:
theorem ofNat_eq_top
  given: {n : Nat} [n.AtLeastTwo]
  statement: (ofNat(n) : Ideal R) = ⊤
  proof: natCast_eq_top (NeZero.ne _)

中文:
定理 of自然数_eq_top
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: (of自然数(n) : 理想 R) = ⊤
  证明: natCast_eq_top (NeZero.ne _)

Depends on / 依赖: NeZero, NeZero.ne, natCast_eq_top
-/
theorem ofNat_eq_top {n : Nat} [n.AtLeastTwo] : (ofNat(n) : Ideal R) = ⊤ :=
  natCast_eq_top (NeZero.ne _)

/--
theorem `pow_eq_zero_of_mem` / 定理 `pow_eq_zero_of_mem`

English:
theorem pow_eq_zero_of_mem
  statement: {I : Ideal R} {n m : Nat} (hnI : I ^ n = 0) (hmn : n <= m) {x : R}
  proof: by
simpa [hnI] using pow_le_pow_right hmn pow_mem_pow hx m

中文:
定理 pow_eq_zero_of_mem
  结论: {I : 理想 R} {n m : 自然数} (hnI : I ^ n = 0) (hmn : n <= m) {x : R}
  证明: by
simpa [hnI] using pow_le_pow_right hmn pow_mem_pow hx m

Depends on / 依赖: pow_le_pow_right, pow_mem_pow
-/
theorem pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (hnI : I ^ n = 0) (hmn : n <= m) {x : R}
    (hx : x in I) : x ^ m = 0 := by
simpa [hnI] using pow_le_pow_right hmn pow_mem_pow hx m

end Semiring

section MulAndRadical

variable {R : Type u} {ι : Type*} [CommSemiring R]
variable {I J K L : Ideal R}

/--
theorem `mul_mem_mul_rev` / 定理 `mul_mem_mul_rev`

English:
theorem mul_mem_mul_rev
  given: {r s} (hr : r in I) (hs : s in J)
  statement: s * r in I * J
  proof: mul_comm r s ▸ mul_mem_mul hr hs

中文:
定理 mul_mem_mul_rev
  条件: {r s} (hr : r in I) (hs : s in J)
  结论: s * r in I * J
  证明: mul_comm r s ▸ mul_mem_mul hr hs

Depends on / 依赖: mul_comm, mul_mem_mul
-/
theorem mul_mem_mul_rev {r s} (hr : r in I) (hs : s in J) : s * r in I * J :=
  mul_comm r s ▸ mul_mem_mul hr hs

/--
theorem `prod_mem_prod` / 定理 `prod_mem_prod`

English:
theorem prod_mem_prod
  given: {ι : Type*} {s : Finset ι} {I : ι -> Ideal R} {x : ι -> R}
  proof: by
  classical
    refine Finset.induction_on s ?_ ?_
    · grind [Submodule.mem_top]
    · grind [mul_mem_mul]

中文:
定理 prod_mem_prod
  条件: {ι : 类型} {s : 有限集 ι} {I : ι -> 理想 R} {x : ι -> R}
  证明: by
  classical
    refine Finset.induction_on s ?_ ?_
    · grind [Submodule.mem_top]
    · grind [mul_mem_mul]

Depends on / 依赖: Finset, Finset.induction_on, Submodule, Submodule.mem_top, classical, induction_on, mem_top, mul_mem_mul
-/
theorem prod_mem_prod {ι : Type*} {s : Finset ι} {I : ι -> Ideal R} {x : ι -> R} :
    (forall i in s, x i in I i) -> (∏ i in s, x i) in ∏ i in s, I i := by
  classical
    refine Finset.induction_on s ?_ ?_
    · grind [Submodule.mem_top]
    · grind [mul_mem_mul]

/--
lemma `sup_pow_add_le_pow_sup_pow` / 引理 `sup_pow_add_le_pow_sup_pow`

English:
lemma sup_pow_add_le_pow_sup_pow
  given: {n m : Nat}
  statement: (I ⊔ J) ^ (n + m) <= I ^ n ⊔ J ^ m
  proof: by
  rw [← Ideal.add_eq_sup]; rw [← Ideal.add_eq_sup]; rw [add_pow]; rw [Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n <= i
  · exact (Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left)))
  · refine (Ideal.mul_le_left.trans

中文:
引理 sup_pow_add_le_pow_sup_pow
  条件: {n m : 自然数}
  结论: (I ⊔ J) ^ (n + m) <= I ^ n ⊔ J ^ m
  证明: by
  rw [← Ideal.add_eq_sup]; rw [← Ideal.add_eq_sup]; rw [add_pow]; rw [Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n <= i
  · exact (Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left)))
  · refine (Ideal.mul_le_left.trans

Depends on / 依赖: Finset, Finset.sup_le, Ideal.add_eq_sup, Ideal.mul_le_left.trans, Ideal.mul_le_right.trans, Ideal.pow_le_pow_right, Ideal.sum_eq_sup, add_eq_sup, add_pow, le_sup_left, le_sup_right, mul_le_left, mul_le_right, pow_le_pow_right, sum_eq_sup, sup_le
-/
lemma sup_pow_add_le_pow_sup_pow {n m : Nat} : (I ⊔ J) ^ (n + m) <= I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup]; rw [← Ideal.add_eq_sup]; rw [add_pow]; rw [Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n <= i
  · exact (Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left)))
  · refine (Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right)))
    lia

variable (I J) in
/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: I * J = J * I
  proof: le_antisymm (mul_le.2 fun _ hrI _ hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun _ hrJ _ hsI => mul_mem_mul_rev hsI hrJ)

中文:
定理 mul_comm
  结论: I * J = J * I
  证明: le_antisymm (mul_le.2 fun _ hrI _ hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun _ hrJ _ hsI => mul_mem_mul_rev hsI hrJ)
-/
protected theorem mul_comm : I * J = J * I :=
  le_antisymm (mul_le.2 fun _ hrI _ hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun _ hrJ _ hsI => mul_mem_mul_rev hsI hrJ)

/--
theorem `mem_span_singleton_mul` / 定理 `mem_span_singleton_mul`

English:
theorem mem_span_singleton_mul
  given: {x y : R} {I : Ideal R}
  statement: x in span {y} * I ↔ exists z in I, y * z = x
  proof: by
  simp only [mul_comm, mem_mul_span_singleton]

@[simp]

中文:
定理 mem_span_singleton_mul
  条件: {x y : R} {I : 理想 R}
  结论: x in span {y} * I ↔ 存在 z in I, y * z = x
  证明: by
  simp only [mul_comm, mem_mul_span_singleton]

@[simp]

Depends on / 依赖: mem_mul_span_singleton, mul_comm
-/
theorem mem_span_singleton_mul {x y : R} {I : Ideal R} : x in span {y} * I ↔ exists z in I, y * z = x := by
  simp only [mul_comm, mem_mul_span_singleton]

@[simp]
/--
lemma `range_mul` / 引理 `range_mul`

English:
lemma range_mul
  statement: (A : Type*) [CommSemiring A] [Module R A]
  proof: by
  aesop (add simp Ideal.mem_span_singleton) (add simp dvd_def)

中文:
引理 range_mul
  结论: (A : 类型) [交换半环 A] [模 R A]
  证明: by
  aesop (add simp Ideal.mem_span_singleton) (add simp dvd_def)

Depends on / 依赖: Ideal.mem_span_singleton, dvd_def, mem_span_singleton
-/
lemma range_mul (A : Type*) [CommSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] (a : A) : LinearMap.range (LinearMap.mul R A a) =
    (Ideal.span {a}).restrictScalars R := by
  aesop (add simp Ideal.mem_span_singleton) (add simp dvd_def)

/--
lemma `range_mul'` / 引理 `range_mul'`

English:
lemma range_mul'
  given: (a : R)
  statement: LinearMap.range (LinearMap.mul R R a) = Ideal.span {a}
  proof: range_mul ..

中文:
引理 range_mul'
  条件: (a : R)
  结论: 线性映射.range (线性映射.mul R R a) = 理想.span {a}
  证明: range_mul ..

Depends on / 依赖: range_mul
-/
lemma range_mul' (a : R) : LinearMap.range (LinearMap.mul R R a) = Ideal.span {a} := range_mul ..

/--
theorem `le_span_singleton_mul_iff` / 定理 `le_span_singleton_mul_iff`

English:
theorem le_span_singleton_mul_iff
  given: {x : R} {I J : Ideal R}
  proof: show (forall {zI} (_ : zI in I), zI in span {x} * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_span_singleton_mul]

中文:
定理 le_span_singleton_mul_iff
  条件: {x : R} {I J : 理想 R}
  证明: show (forall {zI} (_ : zI in I), zI in span {x} * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_span_singleton_mul]

Depends on / 依赖: mem_span_singleton_mul
-/
theorem le_span_singleton_mul_iff {x : R} {I J : Ideal R} :
    I <= span {x} * J ↔ forall zI in I, exists zJ in J, x * zJ = zI :=
  show (forall {zI} (_ : zI in I), zI in span {x} * J) ↔ forall zI in I, exists zJ in J, x * zJ = zI by
    simp only [mem_span_singleton_mul]

/--
theorem `span_singleton_mul_le_iff` / 定理 `span_singleton_mul_le_iff`

English:
theorem span_singleton_mul_le_iff
  given: {x : R} {I J : Ideal R}
  proof: by
  simp [SetLike.le_def, mem_span_singleton_mul]

中文:
定理 span_singleton_mul_le_iff
  条件: {x : R} {I J : 理想 R}
  证明: by
  simp [SetLike.le_def, mem_span_singleton_mul]

Depends on / 依赖: SetLike, SetLike.le_def, le_def, mem_span_singleton_mul
-/
theorem span_singleton_mul_le_iff {x : R} {I J : Ideal R} :
    span {x} * I <= J ↔ forall z in I, x * z in J := by
  simp [SetLike.le_def, mem_span_singleton_mul]

/--
theorem `span_singleton_mul_le_span_singleton_mul` / 定理 `span_singleton_mul_le_span_singleton_mul`

English:
theorem span_singleton_mul_le_span_singleton_mul
  given: {x y : R} {I J : Ideal R}
  proof: by
  simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]

中文:
定理 span_singleton_mul_le_span_singleton_mul
  条件: {x y : R} {I J : 理想 R}
  证明: by
  simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]

Depends on / 依赖: eq_comm, mem_span_singleton_mul, span_singleton_mul_le_iff
-/
theorem span_singleton_mul_le_span_singleton_mul {x y : R} {I J : Ideal R} :
    span {x} * I <= span {y} * J ↔ forall zI in I, exists zJ in J, x * zI = y * zJ := by
  simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]

/--
theorem `span_singleton_mul_right_mono` / 定理 `span_singleton_mul_right_mono`

English:
theorem span_singleton_mul_right_mono
  given: [IsDomain R] {x : R} (hx : x != 0)
  proof: by
  simp_rw [span_singleton_mul_le_span_singleton_mul, mul_right_inj' hx,
    exists_eq_right', SetLike.le_def]

中文:
定理 span_singleton_mul_right_mono
  条件: [是整环 R] {x : R} (hx : x != 0)
  证明: by
  simp_rw [span_singleton_mul_le_span_singleton_mul, mul_right_inj' hx,
    exists_eq_right', SetLike.le_def]

Depends on / 依赖: SetLike, SetLike.le_def, exists_eq_right, le_def, mul_right_inj, simp_rw, span_singleton_mul_le_span_singleton_mul
-/
theorem span_singleton_mul_right_mono [IsDomain R] {x : R} (hx : x != 0) :
    span {x} * I <= span {x} * J ↔ I <= J := by
  simp_rw [span_singleton_mul_le_span_singleton_mul, mul_right_inj' hx,
    exists_eq_right', SetLike.le_def]

/--
theorem `span_singleton_mul_right_inj` / 定理 `span_singleton_mul_right_inj`

English:
theorem span_singleton_mul_right_inj
  given: [IsDomain R] {x : R} (hx : x != 0)
  proof: by
  simp only [le_antisymm_iff, span_singleton_mul_right_mono hx]

中文:
定理 span_singleton_mul_right_inj
  条件: [是整环 R] {x : R} (hx : x != 0)
  证明: by
  simp only [le_antisymm_iff, span_singleton_mul_right_mono hx]

Depends on / 依赖: le_antisymm_iff, span_singleton_mul_right_mono
-/
theorem span_singleton_mul_right_inj [IsDomain R] {x : R} (hx : x != 0) :
    span {x} * I = span {x} * J ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_right_mono hx]

/--
theorem `span_singleton_mul_right_injective` / 定理 `span_singleton_mul_right_injective`

English:
theorem span_singleton_mul_right_injective
  given: [IsDomain R] {x : R} (hx : x != 0)
  proof: fun _ _ =>
  (span_singleton_mul_right_inj hx).mp

中文:
定理 span_singleton_mul_right_injective
  条件: [是整环 R] {x : R} (hx : x != 0)
  证明: fun _ _ =>
  (span_singleton_mul_right_inj hx).mp
-/
theorem span_singleton_mul_right_injective [IsDomain R] {x : R} (hx : x != 0) :
    Function.Injective ((span {x} : Ideal R) * ·) := fun _ _ =>
  (span_singleton_mul_right_inj hx).mp

/--
theorem `span_singleton_mul_left_injective` / 定理 `span_singleton_mul_left_injective`

English:
theorem span_singleton_mul_left_injective
  given: [IsDomain R] {x : R} (hx : x != 0)
  proof: fun _ _ =>
  (span_singleton_mul_left_inj hx).mp

中文:
定理 span_singleton_mul_left_injective
  条件: [是整环 R] {x : R} (hx : x != 0)
  证明: fun _ _ =>
  (span_singleton_mul_left_inj hx).mp
-/
theorem span_singleton_mul_left_injective [IsDomain R] {x : R} (hx : x != 0) :
    Function.Injective fun I : Ideal R => I * span {x} := fun _ _ =>
  (span_singleton_mul_left_inj hx).mp

/--
theorem `eq_span_singleton_mul` / 定理 `eq_span_singleton_mul`

English:
theorem eq_span_singleton_mul
  given: {x : R} (I J : Ideal R)
  proof: by
  simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

中文:
定理 eq_span_singleton_mul
  条件: {x : R} (I J : 理想 R)
  证明: by
  simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

Depends on / 依赖: le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff
-/
theorem eq_span_singleton_mul {x : R} (I J : Ideal R) :
    I = span {x} * J ↔ (forall zI in I, exists zJ in J, x * zJ = zI) ∧ forall z in J, x * z in I := by
  simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

/--
theorem `span_singleton_mul_eq_span_singleton_mul` / 定理 `span_singleton_mul_eq_span_singleton_mul`

English:
theorem span_singleton_mul_eq_span_singleton_mul
  given: {x y : R} (I J : Ideal R)
  proof: by
  simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]

中文:
定理 span_singleton_mul_eq_span_singleton_mul
  条件: {x y : R} (I J : 理想 R)
  证明: by
  simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]

Depends on / 依赖: eq_comm, le_antisymm_iff, span_singleton_mul_le_span_singleton_mul
-/
theorem span_singleton_mul_eq_span_singleton_mul {x y : R} (I J : Ideal R) :
    span {x} * I = span {y} * J ↔
      (forall zI in I, exists zJ in J, x * zI = y * zJ) ∧ forall zJ in J, exists zI in I, x * zI = y * zJ := by
  simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]

/--
theorem `prod_span` / 定理 `prod_span`

English:
theorem prod_span
  given: {ι : Type*} (s : Finset ι) (I : ι -> Set R)
  proof: Submodule.prod_span s I

中文:
定理 prod_span
  条件: {ι : 类型} (s : 有限集 ι) (I : ι -> 集合 R)
  证明: Submodule.prod_span s I

Depends on / 依赖: Submodule, Submodule.prod_span, prod_span
-/
theorem prod_span {ι : Type*} (s : Finset ι) (I : ι -> Set R) :
    (∏ i in s, Ideal.span (I i)) = Ideal.span (∏ i in s, I i) :=
  Submodule.prod_span s I

/--
theorem `prod_span_singleton` / 定理 `prod_span_singleton`

English:
theorem prod_span_singleton
  given: {ι : Type*} (s : Finset ι) (I : ι -> R)
  proof: Submodule.prod_span_singleton s I

@[simp]

中文:
定理 prod_span_singleton
  条件: {ι : 类型} (s : 有限集 ι) (I : ι -> R)
  证明: Submodule.prod_span_singleton s I

@[simp]

Depends on / 依赖: Submodule, Submodule.prod_span_singleton, prod_span_singleton
-/
theorem prod_span_singleton {ι : Type*} (s : Finset ι) (I : ι -> R) :
    (∏ i in s, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} :=
  Submodule.prod_span_singleton s I

@[simp]
/--
theorem `multiset_prod_span_singleton` / 定理 `multiset_prod_span_singleton`

English:
theorem multiset_prod_span_singleton
  given: (m : Multiset R)
  proof: Multiset.induction_on m (by simp) fun a m ih => by
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Ideal.span_singleton_mul_span_singleton]

中文:
定理 multiset_prod_span_singleton
  条件: (m : Multiset R)
  证明: Multiset.induction_on m (by simp) fun a m ih => by
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Ideal.span_singleton_mul_span_singleton]

Depends on / 依赖: Ideal.span_singleton_mul_span_singleton, Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, induction_on, map_cons, prod_cons, span_singleton_mul_span_singleton
-/
theorem multiset_prod_span_singleton (m : Multiset R) :
    (m.map fun x => Ideal.span {x}).prod = Ideal.span ({Multiset.prod m} : Set R) :=
  Multiset.induction_on m (by simp) fun a m ih => by
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Ideal.span_singleton_mul_span_singleton]

open scoped Function in -- required for scoped `on` notation
/--
theorem `finset_inf_span_singleton` / 定理 `finset_inf_span_singleton`

English:
theorem finset_inf_span_singleton
  statement: {ι : Type*} (s : Finset ι) (I : ι -> R)
  proof: by
  ext x
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩

中文:
定理 finset_inf_span_singleton
  结论: {ι : 类型} (s : 有限集 ι) (I : ι -> R)
  证明: by
  ext x
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.prod_dvd_of_coprime, Ideal.mem_span_singleton, Submodule, Submodule.mem_finsetInf, dvd_prod_of_mem, mem_finsetInf, mem_span_singleton, prod_dvd_of_coprime
-/
theorem finset_inf_span_singleton {ι : Type*} (s : Finset ι) (I : ι -> R)
    (hI : Set.Pairwise (↑s) (IsCoprime on I)) :
    (s.inf fun i => Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} := by
  ext x
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩

/--
theorem `iInf_span_singleton` / 定理 `iInf_span_singleton`

English:
theorem iInf_span_singleton
  statement: {ι : Type*} [Fintype ι] {I : ι -> R}
  proof: by
  rw [← Finset.inf_univ_eq_iInf]; rw [finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]

中文:
定理 iInf_span_singleton
  结论: {ι : 类型} [有限类型 ι] {I : ι -> R}
  证明: by
  rw [← Finset.inf_univ_eq_iInf]; rw [finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]

Depends on / 依赖: Finset, Finset.coe_univ, Finset.inf_univ_eq_iInf, Set.pairwise_univ, coe_univ, finset_inf_span_singleton, inf_univ_eq_iInf, pairwise_univ
-/
theorem iInf_span_singleton {ι : Type*} [Fintype ι] {I : ι -> R}
    (hI : forall (i j) (_ : i != j), IsCoprime (I i) (I j)) :
    ⨅ i, span ({I i} : Set R) = span {∏ i, I i} := by
  rw [← Finset.inf_univ_eq_iInf]; rw [finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]

/--
theorem `iInf_span_singleton_natCast` / 定理 `iInf_span_singleton_natCast`

English:
theorem iInf_span_singleton_natCast
  statement: {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  proof: by
  rw [iInf_span_singleton]; rw [Nat.cast_prod]
  exact fun i j h => (hI h).cast

中文:
定理 iInf_span_singleton_natCast
  结论: {R : 类型} [交换环 R] {ι : 类型} [有限类型 ι]
  证明: by
  rw [iInf_span_singleton]; rw [Nat.cast_prod]
  exact fun i j h => (hI h).cast

Depends on / 依赖: Nat.cast_prod, cast_prod, iInf_span_singleton
-/
theorem iInf_span_singleton_natCast {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {I : ι -> Nat} (hI : Pairwise fun i j => (I i).Coprime (I j)) :
    ⨅ (i : ι), span {(I i : R)} = span {((∏ i : ι, I i : Nat) : R)} := by
  rw [iInf_span_singleton]; rw [Nat.cast_prod]
  exact fun i j h => (hI h).cast

/--
theorem `sup_eq_top_iff_isCoprime` / 定理 `sup_eq_top_iff_isCoprime`

English:
theorem sup_eq_top_iff_isCoprime
  given: {R : Type*} [CommSemiring R] (x y : R)
  proof: by
  rw [eq_top_iff_one]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.choose_spec]; rw [← hv.choose_spec] at h1
    exact ⟨_, _, h1⟩
  · exact fun ⟨u, v, h1⟩ =>
      ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton

中文:
定理 sup_eq_top_iff_isCoprime
  条件: {R : 类型} [交换半环 R] (x y : R)
  证明: by
  rw [eq_top_iff_one]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.choose_spec]; rw [← hv.choose_spec] at h1
    exact ⟨_, _, h1⟩
  · exact fun ⟨u, v, h1⟩ =>
      ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton

Depends on / 依赖: Submodule, Submodule.mem_sup, choose_spec, eq_top_iff_one, hu.choose_spec, hv.choose_spec, mem_span_singleton, mem_sup
-/
theorem sup_eq_top_iff_isCoprime {R : Type*} [CommSemiring R] (x y : R) :
    span ({x} : Set R) ⊔ span {y} = ⊤ ↔ IsCoprime x y := by
  rw [eq_top_iff_one]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.choose_spec]; rw [← hv.choose_spec] at h1
    exact ⟨_, _, h1⟩
  · exact fun ⟨u, v, h1⟩ =>
      ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton'.mpr ⟨_, rfl⟩, h1⟩

/--
theorem `multiset_prod_le_inf` / 定理 `multiset_prod_le_inf`

English:
theorem multiset_prod_le_inf
  given: {s : Multiset (Ideal R)}
  statement: s.prod <= s.inf
  proof: by
  refine s.induction_on ?_ ?_
  · rw [Multiset.inf_zero]
    exact le_top
  intro a s ih
  rw [Multiset.prod_cons]; rw [Multiset.inf_cons]
  exact le_trans mul_le_inf (inf_le_inf le_rfl ih)

中文:
定理 multiset_prod_le_inf
  条件: {s : Multiset (理想 R)}
  结论: s.乘积 <= s.下确界
  证明: by
  refine s.induction_on ?_ ?_
  · rw [Multiset.inf_zero]
    exact le_top
  intro a s ih
  rw [Multiset.prod_cons]; rw [Multiset.inf_cons]
  exact le_trans mul_le_inf (inf_le_inf le_rfl ih)

Depends on / 依赖: Multiset, Multiset.inf_cons, Multiset.inf_zero, Multiset.prod_cons, induction_on, inf_cons, inf_le_inf, inf_zero, le_rfl, le_top, le_trans, mul_le_inf, prod_cons, s.induction_on
-/
theorem multiset_prod_le_inf {s : Multiset (Ideal R)} : s.prod <= s.inf := by
  refine s.induction_on ?_ ?_
  · rw [Multiset.inf_zero]
    exact le_top
  intro a s ih
  rw [Multiset.prod_cons]; rw [Multiset.inf_cons]
  exact le_trans mul_le_inf (inf_le_inf le_rfl ih)

/--
theorem `prod_le_inf` / 定理 `prod_le_inf`

English:
theorem prod_le_inf
  given: {s : Finset ι} {f : ι -> Ideal R}
  statement: s.prod f <= s.inf f
  proof: multiset_prod_le_inf

中文:
定理 prod_le_inf
  条件: {s : 有限集 ι} {f : ι -> 理想 R}
  结论: s.乘积 f <= s.下确界 f
  证明: multiset_prod_le_inf

Depends on / 依赖: multiset_prod_le_inf
-/
theorem prod_le_inf {s : Finset ι} {f : ι -> Ideal R} : s.prod f <= s.inf f :=
  multiset_prod_le_inf

/--
theorem `mul_eq_inf_of_coprime` / 定理 `mul_eq_inf_of_coprime`

English:
theorem mul_eq_inf_of_coprime
  given: (h : I ⊔ J = ⊤)
  statement: I * J = I ⊓ J
  proof: le_antisymm mul_le_inf fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_one r ▸
      hst ▸
        (mul_add r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

中文:
定理 mul_eq_inf_of_coprime
  条件: (h : I ⊔ J = ⊤)
  结论: I * J = I ⊓ J
  证明: le_antisymm mul_le_inf fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_one r ▸
      hst ▸
        (mul_add r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

Depends on / 依赖: Ideal.add_mem, Submodule, Submodule.mem_sup, add_mem, eq_top_iff_one, le_antisymm, mem_sup, mul_add, mul_le_inf, mul_mem_mul, mul_mem_mul_rev, mul_one
-/
theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
  le_antisymm mul_le_inf fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_one r ▸
      hst ▸
        (mul_add r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

/--
theorem `sup_prod_eq_top` / 定理 `sup_prod_eq_top`

English:
theorem sup_prod_eq_top
  given: {s : Finset ι} {J : ι -> Ideal R} (h : forall i, i in s -> I ⊔ J i = ⊤)
  proof: Finset.prod_induction _ (fun J => I ⊔ J = ⊤)
    (fun _ _ hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by simp_rw [one_eq_top, sup_top_eq]) h

中文:
定理 sup_prod_eq_top
  条件: {s : 有限集 ι} {J : ι -> 理想 R} (h : 对任意 i, i in s -> I ⊔ J i = ⊤)
  证明: Finset.prod_induction _ (fun J => I ⊔ J = ⊤)
    (fun _ _ hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by simp_rw [one_eq_top, sup_top_eq]) h

Depends on / 依赖: Finset, Finset.prod_induction, one_eq_top, prod_induction, simp_rw, sup_mul_eq_of_coprime_left, sup_top_eq
-/
theorem sup_prod_eq_top {s : Finset ι} {J : ι -> Ideal R} (h : forall i, i in s -> I ⊔ J i = ⊤) :
    (I ⊔ ∏ i in s, J i) = ⊤ :=
  Finset.prod_induction _ (fun J => I ⊔ J = ⊤)
    (fun _ _ hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by simp_rw [one_eq_top, sup_top_eq]) h

/--
theorem `sup_multiset_prod_eq_top` / 定理 `sup_multiset_prod_eq_top`

English:
theorem sup_multiset_prod_eq_top
  given: {s : Multiset (Ideal R)} (h : forall p in s, I ⊔ p = ⊤)
  proof: Multiset.prod_induction (I ⊔ · = ⊤) s (fun _ _ hp hq => (sup_mul_eq_of_coprime_left hp).trans hq)
    (by simp only [one_eq_top, le_top, sup_of_le_right]) h

中文:
定理 sup_multiset_prod_eq_top
  条件: {s : Multiset (理想 R)} (h : 对任意 p in s, I ⊔ p = ⊤)
  证明: Multiset.prod_induction (I ⊔ · = ⊤) s (fun _ _ hp hq => (sup_mul_eq_of_coprime_left hp).trans hq)
    (by simp only [one_eq_top, le_top, sup_of_le_right]) h

Depends on / 依赖: Multiset, Multiset.prod_induction, le_top, one_eq_top, prod_induction, sup_mul_eq_of_coprime_left, sup_of_le_right
-/
theorem sup_multiset_prod_eq_top {s : Multiset (Ideal R)} (h : forall p in s, I ⊔ p = ⊤) :
    I ⊔ s.prod = ⊤ :=
  Multiset.prod_induction (I ⊔ · = ⊤) s (fun _ _ hp hq => (sup_mul_eq_of_coprime_left hp).trans hq)
    (by simp only [one_eq_top, le_top, sup_of_le_right]) h

/--
theorem `prod_sup_eq_top` / 定理 `prod_sup_eq_top`

English:
theorem prod_sup_eq_top
  given: {s : Finset ι} {J : ι -> Ideal R} (h : forall i, i in s -> J i ⊔ I = ⊤)
  proof: by rw [sup_comm, sup_prod_eq_top]; intro i hi; rw [sup_comm, h i hi]

中文:
定理 prod_sup_eq_top
  条件: {s : 有限集 ι} {J : ι -> 理想 R} (h : 对任意 i, i in s -> J i ⊔ I = ⊤)
  证明: by rw [sup_comm, sup_prod_eq_top]; intro i hi; rw [sup_comm, h i hi]

Depends on / 依赖: sup_comm, sup_prod_eq_top
-/
theorem prod_sup_eq_top {s : Finset ι} {J : ι -> Ideal R} (h : forall i, i in s -> J i ⊔ I = ⊤) :
    (∏ i in s, J i) ⊔ I = ⊤ := by rw [sup_comm, sup_prod_eq_top]; intro i hi; rw [sup_comm, h i hi]

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
@[simp]
/--
lemma `multiset_prod_eq_bot` / 引理 `multiset_prod_eq_bot`

English:
lemma multiset_prod_eq_bot
  given: {R : Type*} [CommSemiring R] [IsDomain R] {s : Multiset (Ideal R)}
  proof: Multiset.prod_eq_zero_iff

中文:
引理 multiset_prod_eq_bot
  条件: {R : 类型} [交换半环 R] [是整环 R] {s : Multiset (理想 R)}
  证明: Multiset.prod_eq_zero_iff

Depends on / 依赖: Multiset, Multiset.prod_eq_zero_iff, prod_eq_zero_iff
-/
lemma multiset_prod_eq_bot {R : Type*} [CommSemiring R] [IsDomain R] {s : Multiset (Ideal R)} :
    s.prod = ⊥ ↔ ⊥ in s :=
  Multiset.prod_eq_zero_iff

/--
theorem `isCoprime_iff_codisjoint` / 定理 `isCoprime_iff_codisjoint`

English:
theorem isCoprime_iff_codisjoint
  statement: IsCoprime I J ↔ Codisjoint I J
  proof: by
  rw [IsCoprime]; rw [codisjoint_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J <= I ⊔ J from
      sup_le (mul_le_right.trans le_sup_left) (mul_le_right.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
  

中文:
定理 isCoprime_iff_codisjoint
  结论: IsCoprime I J ↔ Codisjoint I J
  证明: by
  rw [IsCoprime]; rw [codisjoint_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J <= I ⊔ J from
      sup_le (mul_le_right.trans le_sup_left) (mul_le_right.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
  

Depends on / 依赖: IsCoprime, Submodule, Submodule.add_eq_sup, Submodule.mem_top, add_eq_sup, codisjoint_iff, eq_top_iff_one, le_sup_left, le_sup_right, mem_top, mul_le_right, mul_le_right.trans, one_eq_top, sup_le, top_mul
-/
theorem isCoprime_iff_codisjoint : IsCoprime I J ↔ Codisjoint I J := by
  rw [IsCoprime]; rw [codisjoint_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J <= I ⊔ J from
      sup_le (mul_le_right.trans le_sup_left) (mul_le_right.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
    refine ⟨1, 1, ?_⟩
    simpa only [one_eq_top, top_mul, Submodule.add_eq_sup]

/--
theorem `isCoprime_of_isMaximal` / 定理 `isCoprime_of_isMaximal`

English:
theorem isCoprime_of_isMaximal
  given: [I.IsMaximal] [J.IsMaximal] (ne : I != J)
  statement: IsCoprime I J
  proof: by
  rw [isCoprime_iff_codisjoint]; rw [isMaximal_def] at *
  exact IsCoatom.codisjoint_of_ne ‹_› ‹_› ne

中文:
定理 isCoprime_of_isMaximal
  条件: [I.是极大] [J.是极大] (ne : I != J)
  结论: IsCoprime I J
  证明: by
  rw [isCoprime_iff_codisjoint]; rw [isMaximal_def] at *
  exact IsCoatom.codisjoint_of_ne ‹_› ‹_› ne

Depends on / 依赖: IsCoatom, IsCoatom.codisjoint_of_ne, codisjoint_of_ne, isCoprime_iff_codisjoint, isMaximal_def
-/
theorem isCoprime_of_isMaximal [I.IsMaximal] [J.IsMaximal] (ne : I != J) : IsCoprime I J := by
  rw [isCoprime_iff_codisjoint]; rw [isMaximal_def] at *
  exact IsCoatom.codisjoint_of_ne ‹_› ‹_› ne

/--
theorem `isCoprime_iff_add` / 定理 `isCoprime_iff_add`

English:
theorem isCoprime_iff_add
  statement: IsCoprime I J ↔ I + J = 1
  proof: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [add_eq_sup]; rw [one_eq_top]

中文:
定理 isCoprime_iff_add
  结论: IsCoprime I J ↔ I + J = 1
  证明: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [add_eq_sup]; rw [one_eq_top]

Depends on / 依赖: add_eq_sup, codisjoint_iff, isCoprime_iff_codisjoint, one_eq_top
-/
theorem isCoprime_iff_add : IsCoprime I J ↔ I + J = 1 := by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [add_eq_sup]; rw [one_eq_top]

/--
theorem `isCoprime_iff_exists` / 定理 `isCoprime_iff_exists`

English:
theorem isCoprime_iff_exists
  statement: IsCoprime I J ↔ exists i in I, exists j in J, i + j = 1
  proof: by
  rw [← add_eq_one_iff]; rw [isCoprime_iff_add]

中文:
定理 isCoprime_iff_存在
  结论: IsCoprime I J ↔ 存在 i in I, 存在 j in J, i + j = 1
  证明: by
  rw [← add_eq_one_iff]; rw [isCoprime_iff_add]

Depends on / 依赖: add_eq_one_iff, isCoprime_iff_add
-/
theorem isCoprime_iff_exists : IsCoprime I J ↔ exists i in I, exists j in J, i + j = 1 := by
  rw [← add_eq_one_iff]; rw [isCoprime_iff_add]

/--
theorem `isCoprime_iff_sup_eq` / 定理 `isCoprime_iff_sup_eq`

English:
theorem isCoprime_iff_sup_eq
  statement: IsCoprime I J ↔ I ⊔ J = ⊤
  proof: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]

中文:
定理 isCoprime_iff_sup_eq
  结论: IsCoprime I J ↔ I ⊔ J = ⊤
  证明: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]

Depends on / 依赖: codisjoint_iff, isCoprime_iff_codisjoint
-/
theorem isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J = ⊤ := by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]

/--
theorem `coprime_of_no_prime_ge` / 定理 `coprime_of_no_prime_ge`

English:
theorem coprime_of_no_prime_ge
  given: {I J : Ideal R} (h : forall P, I <= P -> J <= P -> ¬IsPrime P)
  proof: by
  rw [isCoprime_iff_sup_eq]
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.isPrime

中文:
定理 coprime_of_no_prime_ge
  条件: {I J : 理想 R} (h : 对任意 P, I <= P -> J <= P -> ¬是素 P)
  证明: by
  rw [isCoprime_iff_sup_eq]
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.isPrime

Depends on / 依赖: Ideal.exists_le_maximal, exists_le_maximal, hP.isPrime, isCoprime_iff_sup_eq, isPrime, le_sup_left, le_sup_right, le_trans
-/
theorem coprime_of_no_prime_ge {I J : Ideal R} (h : forall P, I <= P -> J <= P -> ¬IsPrime P) :
    IsCoprime I J := by
  rw [isCoprime_iff_sup_eq]
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.isPrime

open List in
/--
theorem `isCoprime_tfae` / 定理 `isCoprime_tfae`

English:
theorem isCoprime_tfae
  statement: TFAE [IsCoprime I J, Codisjoint I J, I + J = 1,
  proof: by
  rw [← isCoprime_iff_codisjoint]; rw [← isCoprime_iff_add]; rw [← isCoprime_iff_exists]; rw [← isCoprime_iff_sup_eq]
  simp

中文:
定理 isCoprime_tfae
  结论: TFAE [IsCoprime I J, Codisjoint I J, I + J = 1,
  证明: by
  rw [← isCoprime_iff_codisjoint]; rw [← isCoprime_iff_add]; rw [← isCoprime_iff_exists]; rw [← isCoprime_iff_sup_eq]
  simp

Depends on / 依赖: isCoprime_iff_add, isCoprime_iff_codisjoint, isCoprime_iff_exists, isCoprime_iff_sup_eq
-/
theorem isCoprime_tfae : TFAE [IsCoprime I J, Codisjoint I J, I + J = 1,
    exists i in I, exists j in J, i + j = 1, I ⊔ J = ⊤] := by
  rw [← isCoprime_iff_codisjoint]; rw [← isCoprime_iff_add]; rw [← isCoprime_iff_exists]; rw [← isCoprime_iff_sup_eq]
  simp

/--
theorem `_root_.IsCoprime.codisjoint` / 定理 `_root_.IsCoprime.codisjoint`

English:
theorem _root_.IsCoprime.codisjoint
  given: (h : IsCoprime I J)
  statement: Codisjoint I J
  proof: isCoprime_iff_codisjoint.mp h

中文:
定理 _root_.IsCoprime.codisjoint
  条件: (h : IsCoprime I J)
  结论: Codisjoint I J
  证明: isCoprime_iff_codisjoint.mp h

Depends on / 依赖: isCoprime_iff_codisjoint, isCoprime_iff_codisjoint.mp
-/
theorem _root_.IsCoprime.codisjoint (h : IsCoprime I J) : Codisjoint I J :=
  isCoprime_iff_codisjoint.mp h

/--
theorem `_root_.IsCoprime.add_eq` / 定理 `_root_.IsCoprime.add_eq`

English:
theorem _root_.IsCoprime.add_eq
  given: (h : IsCoprime I J)
  statement: I + J = 1
  proof: isCoprime_iff_add.mp h

中文:
定理 _root_.IsCoprime.add_eq
  条件: (h : IsCoprime I J)
  结论: I + J = 1
  证明: isCoprime_iff_add.mp h

Depends on / 依赖: isCoprime_iff_add, isCoprime_iff_add.mp
-/
theorem _root_.IsCoprime.add_eq (h : IsCoprime I J) : I + J = 1 := isCoprime_iff_add.mp h

/--
theorem `_root_.IsCoprime.exists` / 定理 `_root_.IsCoprime.exists`

English:
theorem _root_.IsCoprime.exists
  given: (h : IsCoprime I J)
  statement: exists i in I, exists j in J, i + j = 1
  proof: isCoprime_iff_exists.mp h

中文:
定理 _root_.IsCoprime.存在
  条件: (h : IsCoprime I J)
  结论: 存在 i in I, 存在 j in J, i + j = 1
  证明: isCoprime_iff_exists.mp h

Depends on / 依赖: isCoprime_iff_exists, isCoprime_iff_exists.mp
-/
theorem _root_.IsCoprime.exists (h : IsCoprime I J) : exists i in I, exists j in J, i + j = 1 :=
  isCoprime_iff_exists.mp h

/--
theorem `_root_.IsCoprime.sup_eq` / 定理 `_root_.IsCoprime.sup_eq`

English:
theorem _root_.IsCoprime.sup_eq
  given: (h : IsCoprime I J)
  statement: I ⊔ J = ⊤
  proof: isCoprime_iff_sup_eq.mp h

中文:
定理 _root_.IsCoprime.sup_eq
  条件: (h : IsCoprime I J)
  结论: I ⊔ J = ⊤
  证明: isCoprime_iff_sup_eq.mp h

Depends on / 依赖: isCoprime_iff_sup_eq, isCoprime_iff_sup_eq.mp
-/
theorem _root_.IsCoprime.sup_eq (h : IsCoprime I J) : I ⊔ J = ⊤ := isCoprime_iff_sup_eq.mp h


/--
theorem `isCoprime_span_singleton_iff` / 定理 `isCoprime_span_singleton_iff`

English:
theorem isCoprime_span_singleton_iff
  given: (x y : R)
  proof: by
  simp_rw [isCoprime_iff_codisjoint, codisjoint_iff, eq_top_iff_one, mem_span_singleton_sup,
    mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

中文:
定理 isCoprime_span_singleton_iff
  条件: (x y : R)
  证明: by
  simp_rw [isCoprime_iff_codisjoint, codisjoint_iff, eq_top_iff_one, mem_span_singleton_sup,
    mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

Depends on / 依赖: codisjoint_iff, eq_top_iff_one, isCoprime_iff_codisjoint, mem_span_singleton, mem_span_singleton_sup, mul_comm, simp_rw
-/
theorem isCoprime_span_singleton_iff (x y : R) :
    IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y := by
  simp_rw [isCoprime_iff_codisjoint, codisjoint_iff, eq_top_iff_one, mem_span_singleton_sup,
    mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

/--
theorem `isCoprime_biInf` / 定理 `isCoprime_biInf`

English:
theorem isCoprime_biInf
  statement: {J : ι -> Ideal R} {s : Finset ι}
  proof: by
  simp only [isCoprime_iff_add, one_eq_top] at hf ⊢
  exact sup_iInf_eq_top hf

中文:
定理 isCoprime_biInf
  结论: {J : ι -> 理想 R} {s : 有限集 ι}
  证明: by
  simp only [isCoprime_iff_add, one_eq_top] at hf ⊢
  exact sup_iInf_eq_top hf

Depends on / 依赖: isCoprime_iff_add, one_eq_top, sup_iInf_eq_top
-/
theorem isCoprime_biInf {J : ι -> Ideal R} {s : Finset ι}
    (hf : forall j in s, IsCoprime I (J j)) : IsCoprime I (⨅ j in s, J j) := by
  simp only [isCoprime_iff_add, one_eq_top] at hf ⊢
  exact sup_iInf_eq_top hf

-- TODO: Deprecate `Ideal.mul_eq_inf_of_coprime` in favor of this lemma.
/--
theorem `mul_eq_inf_of_isCoprime` / 定理 `mul_eq_inf_of_isCoprime`

English:
theorem mul_eq_inf_of_isCoprime
  given: (coprime : IsCoprime I J)
  statement: I * J = I ⊓ J
  proof: (Ideal.mul_eq_inf_of_coprime coprime.sup_eq)

@[deprecated mul_eq_inf_of_isCoprime (since := "2026-03-10")]

中文:
定理 mul_eq_inf_of_isCoprime
  条件: (coprime : IsCoprime I J)
  结论: I * J = I ⊓ J
  证明: (Ideal.mul_eq_inf_of_coprime coprime.sup_eq)

@[deprecated mul_eq_inf_of_isCoprime (since := "2026-03-10")]

Depends on / 依赖: Ideal.mul_eq_inf_of_coprime, coprime, coprime.sup_eq, mul_eq_inf_of_coprime, sup_eq
-/
theorem mul_eq_inf_of_isCoprime (coprime : IsCoprime I J) : I * J = I ⊓ J :=
  (Ideal.mul_eq_inf_of_coprime coprime.sup_eq)

@[deprecated mul_eq_inf_of_isCoprime (since := "2026-03-10")]
/--
theorem `inf_eq_mul_of_isCoprime` / 定理 `inf_eq_mul_of_isCoprime`

English:
theorem inf_eq_mul_of_isCoprime
  given: (coprime : IsCoprime I J)
  statement: I ⊓ J = I * J
  proof: (Ideal.mul_eq_inf_of_coprime coprime.sup_eq).symm

中文:
定理 inf_eq_mul_of_isCoprime
  条件: (coprime : IsCoprime I J)
  结论: I ⊓ J = I * J
  证明: (Ideal.mul_eq_inf_of_coprime coprime.sup_eq).symm

Depends on / 依赖: Ideal.mul_eq_inf_of_coprime, coprime, coprime.sup_eq, mul_eq_inf_of_coprime, sup_eq
-/
theorem inf_eq_mul_of_isCoprime (coprime : IsCoprime I J) : I ⊓ J = I * J :=
  (Ideal.mul_eq_inf_of_coprime coprime.sup_eq).symm

open Function
/--
theorem `prod_eq_iInf_of_pairwise_isCoprime` / 定理 `prod_eq_iInf_of_pairwise_isCoprime`

English:
theorem prod_eq_iInf_of_pairwise_isCoprime
  statement: {s : Finset ι} {J : ι -> Ideal R}
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s hs ih =>
    simp_all only [Finset.iInf_insert, Finset.coe_insert, Set.pairwise_insert, SetLike.mem_coe,
      ne_eq, not_false_eq_true, Finset.prod_insert, forall_const]
    obtain ⟨hp1, hp2⟩ := hp
    rw [Ide

中文:
定理 prod_eq_iInf_of_pairwise_isCoprime
  结论: {s : 有限集 ι} {J : ι -> 理想 R}
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s hs ih =>
    simp_all only [Finset.iInf_insert, Finset.coe_insert, Set.pairwise_insert, SetLike.mem_coe,
      ne_eq, not_false_eq_true, Finset.prod_insert, forall_const]
    obtain ⟨hp1, hp2⟩ := hp
    rw [Ide

Depends on / 依赖: Finset, Finset.coe_insert, Finset.iInf_insert, Finset.induction, Finset.prod_insert, Ideal.mul_eq_inf_of_isCoprime, Set.pairwise_insert, SetLike, SetLike.mem_coe, classical, coe_insert, forall_const, iInf_insert, insert, isCoprime_biInf, mem_coe, mul_eq_inf_of_isCoprime, ne_eq, not_false_eq_true, pairwise_insert
-/
theorem prod_eq_iInf_of_pairwise_isCoprime {s : Finset ι} {J : ι -> Ideal R}
    (hp : (s : Set ι).Pairwise (IsCoprime on J)) :
    ∏ i in s, J i = ⨅ i in s, J i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s hs ih =>
    simp_all only [Finset.iInf_insert, Finset.coe_insert, Set.pairwise_insert, SetLike.mem_coe,
      ne_eq, not_false_eq_true, Finset.prod_insert, forall_const]
    obtain ⟨hp1, hp2⟩ := hp
    rw [Ideal.mul_eq_inf_of_isCoprime (isCoprime_biInf (by grind))]

/--
Definition of `radical` / `radical` 的定义

English:
definition radical
  signature: (I : Ideal R)
  body: { r | exists n : Nat, r ^ n in I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun {_ _} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
  smul_mem' {r s} := fun ⟨n, h⟩ => ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩

中文:
定义 radical
  签名: (I : 理想 R)
  定义体: { r | exists n : Nat, r ^ n in I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun {_ _} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
  smul_mem' {r s} := fun ⟨n, h⟩ => ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩
-/
def radical (I : Ideal R) : Ideal R where
  carrier := { r | exists n : Nat, r ^ n in I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun {_ _} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
  smul_mem' {r s} := fun ⟨n, h⟩ => ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩

/--
theorem `mem_radical_iff` / 定理 `mem_radical_iff`

English:
theorem mem_radical_iff
  given: {r : R}
  statement: r in I.radical ↔ exists n : Nat, r ^ n in I
  proof: Iff.rfl

中文:
定理 mem_radical_iff
  条件: {r : R}
  结论: r in I.radical ↔ 存在 n : 自然数, r ^ n in I
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_radical_iff {r : R} : r in I.radical ↔ exists n : Nat, r ^ n in I := Iff.rfl

/--
Definition of `IsRadical` / `IsRadical` 的定义

English:
definition IsRadical
  signature: (I : Ideal R)
  body: I.radical <= I

中文:
定义 IsRadical
  签名: (I : 理想 R)
  定义体: I.radical <= I

Depends on / 依赖: I.radical, radical
-/
def IsRadical (I : Ideal R) : Prop :=
  I.radical <= I

/--
theorem `le_radical` / 定理 `le_radical`

English:
theorem le_radical
  statement: I <= radical I
  proof: fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩

中文:
定理 le_radical
  结论: I <= radical I
  证明: fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩

Depends on / 依赖: pow_one
-/
theorem le_radical : I <= radical I := fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩

/--
theorem `radical_eq_iff` / 定理 `radical_eq_iff`

English:
theorem radical_eq_iff
  statement: I.radical = I ↔ I.IsRadical
  proof: by
  rw [le_antisymm_iff]; rw [and_iff_left le_radical]; rw [IsRadical]

alias ⟨_, IsRadical.radical⟩ := radical_eq_iff

中文:
定理 radical_eq_iff
  结论: I.radical = I ↔ I.IsRadical
  证明: by
  rw [le_antisymm_iff]; rw [and_iff_left le_radical]; rw [IsRadical]

alias ⟨_, IsRadical.radical⟩ := radical_eq_iff

Depends on / 依赖: IsRadical, and_iff_left, le_antisymm_iff, le_radical
-/
theorem radical_eq_iff : I.radical = I ↔ I.IsRadical := by
  rw [le_antisymm_iff]; rw [and_iff_left le_radical]; rw [IsRadical]

alias ⟨_, IsRadical.radical⟩ := radical_eq_iff

/--
theorem `isRadical_iff_pow_one_lt` / 定理 `isRadical_iff_pow_one_lt`

English:
theorem isRadical_iff_pow_one_lt
  given: (k : Nat) (hk : 1 < k)
  statement: I.IsRadical ↔ forall r, r ^ k in I -> r in I
  proof: ⟨fun h _r hr => h ⟨k, hr⟩, fun h x ⟨n, hx⟩ =>
    k.pow_imp_self_of_one_lt hk _ (fun _ _ => .inr ∘ I.smul_mem _) h n x hx⟩

中文:
定理 isRadical_iff_pow_one_lt
  条件: (k : 自然数) (hk : 1 < k)
  结论: I.IsRadical ↔ 对任意 r, r ^ k in I -> r in I
  证明: ⟨fun h _r hr => h ⟨k, hr⟩, fun h x ⟨n, hx⟩ =>
    k.pow_imp_self_of_one_lt hk _ (fun _ _ => .inr ∘ I.smul_mem _) h n x hx⟩

Depends on / 依赖: I.smul_mem, k.pow_imp_self_of_one_lt, pow_imp_self_of_one_lt, smul_mem
-/
theorem isRadical_iff_pow_one_lt (k : Nat) (hk : 1 < k) : I.IsRadical ↔ forall r, r ^ k in I -> r in I :=
  ⟨fun h _r hr => h ⟨k, hr⟩, fun h x ⟨n, hx⟩ =>
    k.pow_imp_self_of_one_lt hk _ (fun _ _ => .inr ∘ I.smul_mem _) h n x hx⟩

variable (R) in
/--
theorem `radical_top` / 定理 `radical_top`

English:
theorem radical_top
  statement: (radical ⊤ : Ideal R) = ⊤
  proof: (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩

中文:
定理 radical_top
  结论: (radical ⊤ : 理想 R) = ⊤
  证明: (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩

Depends on / 依赖: Submodule, Submodule.mem_top, eq_top_iff_one, mem_top
-/
theorem radical_top : (radical ⊤ : Ideal R) = ⊤ :=
  (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩

/--
theorem `radical_mono` / 定理 `radical_mono`

English:
theorem radical_mono
  given: (H : I <= J)
  statement: radical I <= radical J
  proof: fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩

中文:
定理 radical_mono
  条件: (H : I <= J)
  结论: radical I <= radical J
  证明: fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩
-/
theorem radical_mono (H : I <= J) : radical I <= radical J := fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩

variable (I)

/--
theorem `radical_isRadical` / 定理 `radical_isRadical`

English:
theorem radical_isRadical
  statement: (radical I).IsRadical
  proof: fun r ⟨n, k, hrnki⟩ =>
  ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩

@[simp]

中文:
定理 radical_isRadical
  结论: (radical I).IsRadical
  证明: fun r ⟨n, k, hrnki⟩ =>
  ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩

@[simp]
-/
theorem radical_isRadical : (radical I).IsRadical := fun r ⟨n, k, hrnki⟩ =>
  ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩

@[simp]
/--
theorem `radical_idem` / 定理 `radical_idem`

English:
theorem radical_idem
  statement: radical (radical I) = radical I
  proof: (radical_isRadical I).radical

中文:
定理 radical_idem
  结论: radical (radical I) = radical I
  证明: (radical_isRadical I).radical

Depends on / 依赖: radical, radical_isRadical
-/
theorem radical_idem : radical (radical I) = radical I :=
  (radical_isRadical I).radical

variable {I}

/--
theorem `IsRadical.radical_le_iff` / 定理 `IsRadical.radical_le_iff`

English:
theorem IsRadical.radical_le_iff
  given: (hJ : J.IsRadical)
  statement: I.radical <= J ↔ I <= J
  proof: ⟨le_trans le_radical, fun h => hJ.radical ▸ radical_mono h⟩

中文:
定理 IsRadical.radical_le_iff
  条件: (hJ : J.IsRadical)
  结论: I.radical <= J ↔ I <= J
  证明: ⟨le_trans le_radical, fun h => hJ.radical ▸ radical_mono h⟩

Depends on / 依赖: hJ.radical, le_radical, le_trans, radical, radical_mono
-/
theorem IsRadical.radical_le_iff (hJ : J.IsRadical) : I.radical <= J ↔ I <= J :=
  ⟨le_trans le_radical, fun h => hJ.radical ▸ radical_mono h⟩

/--
theorem `radical_le_radical_iff` / 定理 `radical_le_radical_iff`

English:
theorem radical_le_radical_iff
  statement: radical I <= radical J ↔ I <= radical J
  proof: (radical_isRadical J).radical_le_iff

@[simp]

中文:
定理 radical_le_radical_iff
  结论: radical I <= radical J ↔ I <= radical J
  证明: (radical_isRadical J).radical_le_iff

@[simp]

Depends on / 依赖: radical_isRadical, radical_le_iff
-/
theorem radical_le_radical_iff : radical I <= radical J ↔ I <= radical J :=
  (radical_isRadical J).radical_le_iff

@[simp]
/--
theorem `radical_eq_top` / 定理 `radical_eq_top`

English:
theorem radical_eq_top
  statement: radical I = ⊤ ↔ I = ⊤
  proof: ⟨fun h =>
(eq_top_iff_one _).2
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩

中文:
定理 radical_eq_top
  结论: radical I = ⊤ ↔ I = ⊤
  证明: ⟨fun h =>
(eq_top_iff_one _).2
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩

Depends on / 依赖: eq_top_iff_one, h.symm, one_pow, radical_top
-/
theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
  ⟨fun h =>
(eq_top_iff_one _).2
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩

/--
theorem `IsPrime.isRadical` / 定理 `IsPrime.isRadical`

English:
theorem IsPrime.isRadical
  given: (H : IsPrime I)
  statement: I.IsRadical
  proof: fun _ ⟨n, hrni⟩ =>
  H.mem_of_pow_mem n hrni

中文:
定理 是素.isRadical
  条件: (H : 是素 I)
  结论: I.IsRadical
  证明: fun _ ⟨n, hrni⟩ =>
  H.mem_of_pow_mem n hrni
-/
theorem IsPrime.isRadical (H : IsPrime I) : I.IsRadical := fun _ ⟨n, hrni⟩ =>
  H.mem_of_pow_mem n hrni

/--
theorem `IsPrime.radical` / 定理 `IsPrime.radical`

English:
theorem IsPrime.radical
  given: (H : IsPrime I)
  statement: radical I = I
  proof: IsRadical.radical H.isRadical

中文:
定理 是素.radical
  条件: (H : 是素 I)
  结论: radical I = I
  证明: IsRadical.radical H.isRadical

Depends on / 依赖: H.isRadical, IsRadical, IsRadical.radical, isRadical, radical
-/
theorem IsPrime.radical (H : IsPrime I) : radical I = I :=
  IsRadical.radical H.isRadical

/--
theorem `mem_radical_of_pow_mem` / 定理 `mem_radical_of_pow_mem`

English:
theorem mem_radical_of_pow_mem
  given: {I : Ideal R} {x : R} {m : Nat} (hx : x ^ m in radical I)
  proof: radical_idem I ▸ ⟨m, hx⟩

中文:
定理 mem_radical_of_pow_mem
  条件: {I : 理想 R} {x : R} {m : 自然数} (hx : x ^ m in radical I)
  证明: radical_idem I ▸ ⟨m, hx⟩

Depends on / 依赖: radical_idem
-/
theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : Nat} (hx : x ^ m in radical I) :
    x in radical I :=
  radical_idem I ▸ ⟨m, hx⟩

/--
theorem `disjoint_powers_iff_notMem` / 定理 `disjoint_powers_iff_notMem`

English:
theorem disjoint_powers_iff_notMem
  given: (y : R) (hI : I.IsRadical)
  proof: by
  refine ⟨fun h => Set.disjoint_left.1 h (Submonoid.mem_powers _),
      fun h => disjoint_iff.mpr (eq_bot_iff.mpr ?_)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')

中文:
定理 disjoint_powers_iff_notMem
  条件: (y : R) (hI : I.IsRadical)
  证明: by
  refine ⟨fun h => Set.disjoint_left.1 h (Submonoid.mem_powers _),
      fun h => disjoint_iff.mpr (eq_bot_iff.mpr ?_)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')

Depends on / 依赖: Set.disjoint_left, Submonoid, Submonoid.mem_powers, disjoint_iff, disjoint_iff.mpr, disjoint_left, eq_bot_iff, eq_bot_iff.mpr, le_radical, mem_powers, mem_radical_of_pow_mem
-/
theorem disjoint_powers_iff_notMem (y : R) (hI : I.IsRadical) :
    Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I := by
  refine ⟨fun h => Set.disjoint_left.1 h (Submonoid.mem_powers _),
      fun h => disjoint_iff.mpr (eq_bot_iff.mpr ?_)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')

/--
theorem `disjoint_powers_iff_notMem_of_isPrime` / 定理 `disjoint_powers_iff_notMem_of_isPrime`

English:
theorem disjoint_powers_iff_notMem_of_isPrime
  given: [I.IsPrime] (y : R)
  proof: disjoint_powers_iff_notMem y (IsPrime.isRadical ‹_›)

中文:
定理 disjoint_powers_iff_notMem_of_isPrime
  条件: [I.是素] (y : R)
  证明: disjoint_powers_iff_notMem y (IsPrime.isRadical ‹_›)

Depends on / 依赖: IsPrime, IsPrime.isRadical, disjoint_powers_iff_notMem, isRadical
-/
theorem disjoint_powers_iff_notMem_of_isPrime [I.IsPrime] (y : R) :
    Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I :=
  disjoint_powers_iff_notMem y (IsPrime.isRadical ‹_›)

variable (I J)

/--
theorem `radical_sup` / 定理 `radical_sup`

English:
theorem radical_sup
  statement: radical (I ⊔ J) = radical (radical I ⊔ radical J)
  proof: le_antisymm (radical_mono <| sup_le_sup le_radical le_radical)
radical_le_radical_iff.2 sup_le (radical_mono le_sup_left) (radical_mono le_sup_right)

中文:
定理 radical_sup
  结论: radical (I ⊔ J) = radical (radical I ⊔ radical J)
  证明: le_antisymm (radical_mono <| sup_le_sup le_radical le_radical)
radical_le_radical_iff.2 sup_le (radical_mono le_sup_left) (radical_mono le_sup_right)

Depends on / 依赖: le_antisymm, le_radical, le_sup_left, le_sup_right, radical_le_radical_iff, radical_mono, sup_le, sup_le_sup
-/
theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
le_antisymm (radical_mono <| sup_le_sup le_radical le_radical)
radical_le_radical_iff.2 sup_le (radical_mono le_sup_left) (radical_mono le_sup_right)

/--
theorem `radical_inf` / 定理 `radical_inf`

English:
theorem radical_inf
  statement: radical (I ⊓ J) = radical I ⊓ radical J
  proof: le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
    fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
      (pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩

中文:
定理 radical_inf
  结论: radical (I ⊓ J) = radical I ⊓ radical J
  证明: le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
    fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
      (pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩

Depends on / 依赖: I.mul_mem_right, J.mul_mem_left, inf_le_left, inf_le_right, le_antisymm, le_inf, mul_mem_left, mul_mem_right, pow_add, radical_mono
-/
theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
  le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
    fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
      (pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩

variable {I J} in
/--
theorem `IsRadical.inf` / 定理 `IsRadical.inf`

English:
theorem IsRadical.inf
  given: (hI : IsRadical I) (hJ : IsRadical J)
  statement: IsRadical (I ⊓ J)
  proof: by
  rw [IsRadical]; rw [radical_inf]; exact inf_le_inf hI hJ

中文:
定理 IsRadical.下确界
  条件: (hI : IsRadical I) (hJ : IsRadical J)
  结论: IsRadical (I ⊓ J)
  证明: by
  rw [IsRadical]; rw [radical_inf]; exact inf_le_inf hI hJ

Depends on / 依赖: IsRadical, inf_le_inf, radical_inf
-/
theorem IsRadical.inf (hI : IsRadical I) (hJ : IsRadical J) : IsRadical (I ⊓ J) := by
  rw [IsRadical]; rw [radical_inf]; exact inf_le_inf hI hJ

/--
lemma `isRadical_bot_iff` / 引理 `isRadical_bot_iff`

English:
lemma isRadical_bot_iff
  statement: (⊥ : Ideal R).IsRadical ↔ IsReduced R
  proof: by
  simp only [IsRadical, SetLike.le_def, Ideal.mem_radical_iff, Ideal.mem_bot,
    forall_exists_index, isReduced_iff, IsNilpotent]

中文:
引理 isRadical_bot_iff
  结论: (⊥ : 理想 R).IsRadical ↔ 是既约 R
  证明: by
  simp only [IsRadical, SetLike.le_def, Ideal.mem_radical_iff, Ideal.mem_bot,
    forall_exists_index, isReduced_iff, IsNilpotent]

Depends on / 依赖: Ideal.mem_bot, Ideal.mem_radical_iff, IsNilpotent, IsRadical, SetLike, SetLike.le_def, forall_exists_index, isReduced_iff, le_def, mem_bot, mem_radical_iff
-/
lemma isRadical_bot_iff : (⊥ : Ideal R).IsRadical ↔ IsReduced R := by
  simp only [IsRadical, SetLike.le_def, Ideal.mem_radical_iff, Ideal.mem_bot,
    forall_exists_index, isReduced_iff, IsNilpotent]

/--
lemma `isRadical_bot` / 引理 `isRadical_bot`

English:
lemma isRadical_bot
  given: [IsReduced R]
  statement: (⊥ : Ideal R).IsRadical
  proof: by rwa [isRadical_bot_iff]

中文:
引理 isRadical_bot
  条件: [是既约 R]
  结论: (⊥ : 理想 R).IsRadical
  证明: by rwa [isRadical_bot_iff]

Depends on / 依赖: isRadical_bot_iff
-/
lemma isRadical_bot [IsReduced R] : (⊥ : Ideal R).IsRadical := by rwa [isRadical_bot_iff]

/--
Definition of `radicalInfTopHom` / `radicalInfTopHom` 的定义

English:
definition radicalInfTopHom
  signature: : InfTopHom (Ideal R) (Ideal R) where
  body: radical
  map_inf' := radical_inf
  map_top' := radical_top _

@[simp]

中文:
定义 radicalInfTopHom
  签名: : InfTop态射 (理想 R) (理想 R) where
  定义体: radical
  map_inf' := radical_inf
  map_top' := radical_top _

@[simp]

Depends on / 依赖: radical
-/
def radicalInfTopHom : InfTopHom (Ideal R) (Ideal R) where
  toFun := radical
  map_inf' := radical_inf
  map_top' := radical_top _

@[simp]
/--
lemma `radicalInfTopHom_apply` / 引理 `radicalInfTopHom_apply`

English:
lemma radicalInfTopHom_apply
  given: (I : Ideal R)
  statement: radicalInfTopHom I = radical I
  proof: rfl

中文:
引理 radicalInfTopHom_apply
  条件: (I : 理想 R)
  结论: radicalInfTopHom I = radical I
  证明: rfl
-/
lemma radicalInfTopHom_apply (I : Ideal R) : radicalInfTopHom I = radical I := rfl

open Finset in
/--
lemma `radical_finset_inf` / 引理 `radical_finset_inf`

English:
lemma radical_finset_inf
  statement: {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i in s)
  proof: by
  rw [← radicalInfTopHom_apply]; rw [map_finset_inf]; rw [← Finset.inf'_eq_inf ⟨_]; rw [hi⟩]
  exact Finset.inf'_eq_of_forall _ _ hs

中文:
引理 radical_finset_inf
  结论: {ι} {s : 有限集 ι} {f : ι -> 理想 R} {i : ι} (hi : i in s)
  证明: by
  rw [← radicalInfTopHom_apply]; rw [map_finset_inf]; rw [← Finset.inf'_eq_inf ⟨_]; rw [hi⟩]
  exact Finset.inf'_eq_of_forall _ _ hs

Depends on / 依赖: Finset, Finset.inf, _eq_inf, _eq_of_forall, map_finset_inf, radicalInfTopHom_apply
-/
lemma radical_finset_inf {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i in s)
    (hs : forall ⦃y⦄, y in s -> (f y).radical = (f i).radical) :
    (s.inf f).radical = (f i).radical := by
  rw [← radicalInfTopHom_apply]; rw [map_finset_inf]; rw [← Finset.inf'_eq_inf ⟨_]; rw [hi⟩]
  exact Finset.inf'_eq_of_forall _ _ hs

/--
theorem `radical_iInf_le` / 定理 `radical_iInf_le`

English:
theorem radical_iInf_le
  given: {ι} (I : ι -> Ideal R)
  statement: radical (⨅ i, I i) <= ⨅ i, radical (I i)
  proof: le_iInf fun _ => radical_mono (iInf_le _ _)

中文:
定理 radical_iInf_le
  条件: {ι} (I : ι -> 理想 R)
  结论: radical (⨅ i, I i) <= ⨅ i, radical (I i)
  证明: le_iInf fun _ => radical_mono (iInf_le _ _)

Depends on / 依赖: iInf_le, le_iInf, radical_mono
-/
theorem radical_iInf_le {ι} (I : ι -> Ideal R) : radical (⨅ i, I i) <= ⨅ i, radical (I i) :=
  le_iInf fun _ => radical_mono (iInf_le _ _)

/--
theorem `isRadical_iInf` / 定理 `isRadical_iInf`

English:
theorem isRadical_iInf
  given: {ι} (I : ι -> Ideal R) (hI : forall i, IsRadical (I i))
  statement: IsRadical (⨅ i, I i)
  proof: (radical_iInf_le I).trans (iInf_mono hI)

中文:
定理 isRadical_iInf
  条件: {ι} (I : ι -> 理想 R) (hI : 对任意 i, IsRadical (I i))
  结论: IsRadical (⨅ i, I i)
  证明: (radical_iInf_le I).trans (iInf_mono hI)

Depends on / 依赖: iInf_mono, radical_iInf_le
-/
theorem isRadical_iInf {ι} (I : ι -> Ideal R) (hI : forall i, IsRadical (I i)) : IsRadical (⨅ i, I i) :=
  (radical_iInf_le I).trans (iInf_mono hI)

/--
theorem `radical_mul` / 定理 `radical_mul`

English:
theorem radical_mul
  statement: radical (I * J) = radical I ⊓ radical J
  proof: by
  refine le_antisymm ?_ fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩
have := radical_mono mul_le_inf (I := I) (J := J)
  simp_rw [radical_inf I J] at this
  assumption

中文:
定理 radical_mul
  结论: radical (I * J) = radical I ⊓ radical J
  证明: by
  refine le_antisymm ?_ fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩
have := radical_mono mul_le_inf (I := I) (J := J)
  simp_rw [radical_inf I J] at this
  assumption

Depends on / 依赖: le_antisymm, mul_le_inf, mul_mem_mul, pow_add, radical_inf, radical_mono, simp_rw
-/
theorem radical_mul : radical (I * J) = radical I ⊓ radical J := by
  refine le_antisymm ?_ fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩
have := radical_mono mul_le_inf (I := I) (J := J)
  simp_rw [radical_inf I J] at this
  assumption

variable {I J}

/--
theorem `IsPrime.radical_le_iff` / 定理 `IsPrime.radical_le_iff`

English:
theorem IsPrime.radical_le_iff
  given: (hJ : IsPrime J)
  statement: I.radical <= J ↔ I <= J
  proof: IsRadical.radical_le_iff hJ.isRadical

中文:
定理 是素.radical_le_iff
  条件: (hJ : 是素 J)
  结论: I.radical <= J ↔ I <= J
  证明: IsRadical.radical_le_iff hJ.isRadical

Depends on / 依赖: IsRadical, IsRadical.radical_le_iff, hJ.isRadical, isRadical, radical_le_iff
-/
theorem IsPrime.radical_le_iff (hJ : IsPrime J) : I.radical <= J ↔ I <= J :=
  IsRadical.radical_le_iff hJ.isRadical

/--
theorem `radical_eq_sInf` / 定理 `radical_eq_sInf`

English:
theorem radical_eq_sInf
  given: (I : Ideal R)
  statement: radical I = sInf { J : Ideal R | I <= J ∧ IsPrime J }
  proof: le_antisymm (le_sInf fun _ hJ => hJ.2.radical_le_iff.2 hJ.1) fun r hr =>
    by_contradiction fun hri =>
      let ⟨m, hIm, hm⟩ :=
        zorn_le_nonempty₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sSup c, fun ⟨n, hrnc⟩ =>
              let ⟨_, hyc, hrny⟩ := (Sub

中文:
定理 radical_eq_sInf
  条件: (I : 理想 R)
  结论: radical I = sInf { J : 理想 R | I <= J ∧ 是素 J }
  证明: le_antisymm (le_sInf fun _ hJ => hJ.2.radical_le_iff.2 hJ.1) fun r hr =>
    by_contradiction fun hri =>
      let ⟨m, hIm, hm⟩ :=
        zorn_le_nonempty₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sSup c, fun ⟨n, hrnc⟩ =>
              let ⟨_, hyc, hrny⟩ := (Sub

Depends on / 依赖: Submodule, Submodule.mem_sSup_of_directed, by_contradiction, directedOn, eq_of_l, hcc.directedOn, hm.eq_of_l, hm.prop, le_antisymm, le_sInf, le_sSup, mem_sSup_of_directed, radical, radical_le_iff
-/
theorem radical_eq_sInf (I : Ideal R) : radical I = sInf { J : Ideal R | I <= J ∧ IsPrime J } :=
  le_antisymm (le_sInf fun _ hJ => hJ.2.radical_le_iff.2 hJ.1) fun r hr =>
    by_contradiction fun hri =>
      let ⟨m, hIm, hm⟩ :=
        zorn_le_nonempty₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sSup c, fun ⟨n, hrnc⟩ =>
              let ⟨_, hyc, hrny⟩ := (Submodule.mem_sSup_of_directed ⟨y, hyc⟩ hcc.directedOn).1 hrnc
              hc hyc ⟨n, hrny⟩,
              fun _ => le_sSup⟩)
          I hri
      have hrm : r ∉ radical m := hm.prop
      have : forall x ∉ m, r in radical (m ⊔ span {x}) := fun x hxm =>
by_contradiction fun hrmx => hxm by
          rw [hm.eq_of_le hrmx le_sup_left]
exact Submodule.mem_sup_right mem_span_singleton_self x
      have : IsPrime m :=
        ⟨by rintro rfl; rw [radical_top] at hrm; exact hrm trivial, fun {x y} hxym =>
          or_iff_not_imp_left.2 fun hxm =>
            by_contradiction fun hym =>
              let ⟨n, hrn⟩ := this _ hxm
              let ⟨p, hpm, q, hq, hpqrn⟩ := Submodule.mem_sup.1 hrn
              let ⟨c, hcxq⟩ := mem_span_singleton'.1 hq
              let ⟨k, hrk⟩ := this _ hym
              let ⟨f, hfm, g, hg, hfgrk⟩ := Submodule.mem_sup.1 hrk
              let ⟨d, hdyg⟩ := mem_span_singleton'.1 hg
              hrm
                ⟨n + k, by
                  rw [pow_add]; rw [← hpqrn]; rw [← hcxq]; rw [← hfgrk]; rw [← hdyg]; rw [add_mul]; rw [mul_add (c * x)]; rw [mul_assoc c x (d * y)]; rw [mul_left_comm x]; rw [← mul_assoc]
                  refine
                    m.add_mem (m.mul_mem_right _ hpm)
                    (m.add_mem (m.mul_mem_left _ hfm) (m.mul_mem_left _ hxym))⟩⟩
hrm
      this.radical.symm ▸ (sInf_le ⟨hIm, this⟩ : sInf { J : Ideal R | I <= J ∧ IsPrime J } <= m) hr

@[deprecated isRadical_bot (since := "2026-08-03")]
/--
theorem `isRadical_bot_of_noZeroDivisors` / 定理 `isRadical_bot_of_noZeroDivisors`

English:
theorem isRadical_bot_of_noZeroDivisors
  given: {R} [CommSemiring R] [NoZeroDivisors R]
  proof: isRadical_bot

@[simp]

中文:
定理 isRadical_bot_of_noZeroDivisors
  条件: {R} [交换半环 R] [无零因子 R]
  证明: isRadical_bot

@[simp]

Depends on / 依赖: isRadical_bot
-/
theorem isRadical_bot_of_noZeroDivisors {R} [CommSemiring R] [NoZeroDivisors R] :
    (⊥ : Ideal R).IsRadical := isRadical_bot

@[simp]
/--
theorem `radical_bot_of_isReduced` / 定理 `radical_bot_of_isReduced`

English:
theorem radical_bot_of_isReduced
  given: {R : Type u} [CommSemiring R] [IsReduced R]
  proof: eq_bot_iff.2 isRadical_bot

@[deprecated (since := "2026-08-03")]
alias radical_bot_of_noZeroDivisors := radical_bot_of_isReduced

中文:
定理 radical_bot_of_isReduced
  条件: {R : 类型u} [交换半环 R] [是既约 R]
  证明: eq_bot_iff.2 isRadical_bot

@[deprecated (since := "2026-08-03")]
alias radical_bot_of_noZeroDivisors := radical_bot_of_isReduced

Depends on / 依赖: eq_bot_iff, isRadical_bot
-/
theorem radical_bot_of_isReduced {R : Type u} [CommSemiring R] [IsReduced R] :
    radical (⊥ : Ideal R) = ⊥ :=
  eq_bot_iff.2 isRadical_bot

@[deprecated (since := "2026-08-03")]
alias radical_bot_of_noZeroDivisors := radical_bot_of_isReduced

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IdemCommSemiring (Ideal R)
  body: inferInstance

中文:
实例 :
  签名: IdemCommSemiring (理想 R)
  定义体: inferInstance
-/
instance : IdemCommSemiring (Ideal R) :=
  inferInstance

variable (I)

/--
lemma `radical_pow` / 引理 `radical_pow`

English:
lemma radical_pow
  statement: forall {n}, n != 0 -> radical (I ^ n) = radical I

中文:
引理 radical_pow
  结论: 对任意 {n}, n != 0 -> radical (I ^ n) = radical I
-/
lemma radical_pow : forall {n}, n != 0 -> radical (I ^ n) = radical I
  | 1, _ => by simp
  | n + 2, _ => by rw [pow_succ, radical_mul, radical_pow n.succ_ne_zero, inf_idem]

/--
theorem `IsPrime.mul_le` / 定理 `IsPrime.mul_le`

English:
theorem IsPrime.mul_le
  given: {I J P : Ideal R} (hp : IsPrime P)
  statement: I * J <= P ↔ I <= P ∨ J <= P
  proof: by
  rw [or_comm]; rw [Ideal.mul_le]
  simp_rw [hp.mul_mem_iff_mem_or_mem, SetLike.le_def, ← forall_or_left, or_comm, forall_or_left]

中文:
定理 是素.mul_le
  条件: {I J P : 理想 R} (hp : 是素 P)
  结论: I * J <= P ↔ I <= P ∨ J <= P
  证明: by
  rw [or_comm]; rw [Ideal.mul_le]
  simp_rw [hp.mul_mem_iff_mem_or_mem, SetLike.le_def, ← forall_or_left, or_comm, forall_or_left]

Depends on / 依赖: Ideal.mul_le, SetLike, SetLike.le_def, forall_or_left, hp.mul_mem_iff_mem_or_mem, le_def, mul_le, mul_mem_iff_mem_or_mem, or_comm, simp_rw
-/
theorem IsPrime.mul_le {I J P : Ideal R} (hp : IsPrime P) : I * J <= P ↔ I <= P ∨ J <= P := by
  rw [or_comm]; rw [Ideal.mul_le]
  simp_rw [hp.mul_mem_iff_mem_or_mem, SetLike.le_def, ← forall_or_left, or_comm, forall_or_left]

/--
theorem `IsPrime.inf_le` / 定理 `IsPrime.inf_le`

English:
theorem IsPrime.inf_le
  given: {I J P : Ideal R} (hp : IsPrime P)
  statement: I ⊓ J <= P ↔ I <= P ∨ J <= P
  proof: ⟨fun h => hp.mul_le.1 mul_le_inf.trans h, fun h => h.elim inf_le_left.trans inf_le_right.trans⟩

中文:
定理 是素.inf_le
  条件: {I J P : 理想 R} (hp : 是素 P)
  结论: I ⊓ J <= P ↔ I <= P ∨ J <= P
  证明: ⟨fun h => hp.mul_le.1 mul_le_inf.trans h, fun h => h.elim inf_le_left.trans inf_le_right.trans⟩

Depends on / 依赖: h.elim, hp.mul_le, inf_le_left, inf_le_left.trans, inf_le_right, inf_le_right.trans, mul_le, mul_le_inf, mul_le_inf.trans
-/
theorem IsPrime.inf_le {I J P : Ideal R} (hp : IsPrime P) : I ⊓ J <= P ↔ I <= P ∨ J <= P :=
⟨fun h => hp.mul_le.1 mul_le_inf.trans h, fun h => h.elim inf_le_left.trans inf_le_right.trans⟩

/--
theorem `IsPrime.multiset_prod_le` / 定理 `IsPrime.multiset_prod_le`

English:
theorem IsPrime.multiset_prod_le
  given: {s : Multiset (Ideal R)} {P : Ideal R} (hp : IsPrime P)
  proof: s.induction_on (by simp [hp.ne_top]) fun I s ih => by simp [hp.mul_le, ih]

中文:
定理 是素.multiset_prod_le
  条件: {s : Multiset (理想 R)} {P : 理想 R} (hp : 是素 P)
  证明: s.induction_on (by simp [hp.ne_top]) fun I s ih => by simp [hp.mul_le, ih]

Depends on / 依赖: hp.mul_le, hp.ne_top, induction_on, mul_le, ne_top, s.induction_on
-/
theorem IsPrime.multiset_prod_le {s : Multiset (Ideal R)} {P : Ideal R} (hp : IsPrime P) :
    s.prod <= P ↔ exists I in s, I <= P :=
  s.induction_on (by simp [hp.ne_top]) fun I s ih => by simp [hp.mul_le, ih]

/--
theorem `IsPrime.multiset_prod_map_le` / 定理 `IsPrime.multiset_prod_map_le`

English:
theorem IsPrime.multiset_prod_map_le
  statement: {s : Multiset ι} (f : ι -> Ideal R) {P : Ideal R}
  proof: by
  simp_rw [hp.multiset_prod_le, Multiset.mem_map, exists_exists_and_eq_and]

中文:
定理 是素.multiset_prod_map_le
  结论: {s : Multiset ι} (f : ι -> 理想 R) {P : 理想 R}
  证明: by
  simp_rw [hp.multiset_prod_le, Multiset.mem_map, exists_exists_and_eq_and]

Depends on / 依赖: Multiset, Multiset.mem_map, exists_exists_and_eq_and, hp.multiset_prod_le, mem_map, multiset_prod_le, simp_rw
-/
theorem IsPrime.multiset_prod_map_le {s : Multiset ι} (f : ι -> Ideal R) {P : Ideal R}
    (hp : IsPrime P) : (s.map f).prod <= P ↔ exists i in s, f i <= P := by
  simp_rw [hp.multiset_prod_le, Multiset.mem_map, exists_exists_and_eq_and]

/--
theorem `IsPrime.multiset_prod_mem_iff_exists_mem` / 定理 `IsPrime.multiset_prod_mem_iff_exists_mem`

English:
theorem IsPrime.multiset_prod_mem_iff_exists_mem
  given: {I : Ideal R} (hI : I.IsPrime) (s : Multiset R)
  proof: by
  simpa using (hI.multiset_prod_map_le (span {·}))

中文:
定理 是素.multiset_prod_mem_iff_存在_mem
  条件: {I : 理想 R} (hI : I.是素) (s : Multiset R)
  证明: by
  simpa using (hI.multiset_prod_map_le (span {·}))

Depends on / 依赖: hI.multiset_prod_map_le, multiset_prod_map_le
-/
theorem IsPrime.multiset_prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Multiset R) :
    s.prod in I ↔ exists p in s, p in I := by
  simpa using (hI.multiset_prod_map_le (span {·}))

/--
theorem `IsPrime.pow_le_iff` / 定理 `IsPrime.pow_le_iff`

English:
theorem IsPrime.pow_le_iff
  given: {I P : Ideal R} [hP : P.IsPrime] {n : Nat} (hn : n != 0)
  proof: by
  have h : (Multiset.replicate n I).prod <= P ↔ _ := hP.multiset_prod_le
  simp_rw [Multiset.prod_replicate, Multiset.mem_replicate, ne_eq, hn, not_false_eq_true,
    true_and, exists_eq_left] at h
  exact h

中文:
定理 是素.pow_le_iff
  条件: {I P : 理想 R} [hP : P.是素] {n : 自然数} (hn : n != 0)
  证明: by
  have h : (Multiset.replicate n I).prod <= P ↔ _ := hP.multiset_prod_le
  simp_rw [Multiset.prod_replicate, Multiset.mem_replicate, ne_eq, hn, not_false_eq_true,
    true_and, exists_eq_left] at h
  exact h

Depends on / 依赖: Multiset, Multiset.mem_replicate, Multiset.prod_replicate, Multiset.replicate, exists_eq_left, hP.multiset_prod_le, mem_replicate, multiset_prod_le, ne_eq, not_false_eq_true, prod_replicate, replicate, simp_rw, true_and
-/
theorem IsPrime.pow_le_iff {I P : Ideal R} [hP : P.IsPrime] {n : Nat} (hn : n != 0) :
    I ^ n <= P ↔ I <= P := by
  have h : (Multiset.replicate n I).prod <= P ↔ _ := hP.multiset_prod_le
  simp_rw [Multiset.prod_replicate, Multiset.mem_replicate, ne_eq, hn, not_false_eq_true,
    true_and, exists_eq_left] at h
  exact h

/--
theorem `IsPrime.le_of_pow_le` / 定理 `IsPrime.le_of_pow_le`

English:
theorem IsPrime.le_of_pow_le
  given: {I P : Ideal R} [hP : P.IsPrime] {n : Nat} (h : I ^ n <= P)
  proof: by
  by_cases hn : n = 0
  · rw [hn, pow_zero, one_eq_top] at h
    exact fun ⦃_⦄ _ => h Submodule.mem_top
  · exact (pow_le_iff hn).mp h

中文:
定理 是素.le_of_pow_le
  条件: {I P : 理想 R} [hP : P.是素] {n : 自然数} (h : I ^ n <= P)
  证明: by
  by_cases hn : n = 0
  · rw [hn, pow_zero, one_eq_top] at h
    exact fun ⦃_⦄ _ => h Submodule.mem_top
  · exact (pow_le_iff hn).mp h

Depends on / 依赖: Submodule, Submodule.mem_top, mem_top, one_eq_top, pow_le_iff, pow_zero
-/
theorem IsPrime.le_of_pow_le {I P : Ideal R} [hP : P.IsPrime] {n : Nat} (h : I ^ n <= P) :
    I <= P := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, one_eq_top] at h
    exact fun ⦃_⦄ _ => h Submodule.mem_top
  · exact (pow_le_iff hn).mp h

/--
theorem `IsPrime.prod_le` / 定理 `IsPrime.prod_le`

English:
theorem IsPrime.prod_le
  given: {s : Finset ι} {f : ι -> Ideal R} {P : Ideal R} (hp : IsPrime P)
  proof: hp.multiset_prod_map_le f

中文:
定理 是素.prod_le
  条件: {s : 有限集 ι} {f : ι -> 理想 R} {P : 理想 R} (hp : 是素 P)
  证明: hp.multiset_prod_map_le f

Depends on / 依赖: hp.multiset_prod_map_le, multiset_prod_map_le
-/
theorem IsPrime.prod_le {s : Finset ι} {f : ι -> Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.prod f <= P ↔ exists i in s, f i <= P :=
  hp.multiset_prod_map_le f

/--
theorem `IsPrime.prod_mem_iff` / 定理 `IsPrime.prod_mem_iff`

English:
theorem IsPrime.prod_mem_iff
  given: {s : Finset ι} {x : ι -> R} {p : Ideal R} [hp : p.IsPrime]
  proof: by
  simp_rw [← span_singleton_le_iff_mem, ← prod_span_singleton]
  exact hp.prod_le

中文:
定理 是素.prod_mem_iff
  条件: {s : 有限集 ι} {x : ι -> R} {p : 理想 R} [hp : p.是素]
  证明: by
  simp_rw [← span_singleton_le_iff_mem, ← prod_span_singleton]
  exact hp.prod_le

Depends on / 依赖: hp.prod_le, prod_le, prod_span_singleton, simp_rw, span_singleton_le_iff_mem
-/
theorem IsPrime.prod_mem_iff {s : Finset ι} {x : ι -> R} {p : Ideal R} [hp : p.IsPrime] :
    ∏ i in s, x i in p ↔ exists i in s, x i in p := by
  simp_rw [← span_singleton_le_iff_mem, ← prod_span_singleton]
  exact hp.prod_le

/--
theorem `IsPrime.prod_mem_iff_exists_mem` / 定理 `IsPrime.prod_mem_iff_exists_mem`

English:
theorem IsPrime.prod_mem_iff_exists_mem
  given: {I : Ideal R} (hI : I.IsPrime) (s : Finset R)
  proof: by
  rw [Finset.prod_eq_multiset_prod]; rw [Multiset.map_id']
  exact hI.multiset_prod_mem_iff_exists_mem s.val

中文:
定理 是素.prod_mem_iff_存在_mem
  条件: {I : 理想 R} (hI : I.是素) (s : 有限集 R)
  证明: by
  rw [Finset.prod_eq_multiset_prod]; rw [Multiset.map_id']
  exact hI.multiset_prod_mem_iff_exists_mem s.val

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Multiset, Multiset.map_id, hI.multiset_prod_mem_iff_exists_mem, map_id, multiset_prod_mem_iff_exists_mem, prod_eq_multiset_prod, s.val
-/
theorem IsPrime.prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Finset R) :
    s.prod (fun x => x) in I ↔ exists p in s, p in I := by
  rw [Finset.prod_eq_multiset_prod]; rw [Multiset.map_id']
  exact hI.multiset_prod_mem_iff_exists_mem s.val

/--
theorem `IsPrime.inf_le'` / 定理 `IsPrime.inf_le'`

English:
theorem IsPrime.inf_le'
  given: {s : Finset ι} {f : ι -> Ideal R} {P : Ideal R} (hp : IsPrime P)
  proof: ⟨fun h => hp.prod_le.1 prod_le_inf.trans h, fun ⟨_, his, hip⟩ => (Finset.inf_le his).trans hip⟩

中文:
定理 是素.inf_le'
  条件: {s : 有限集 ι} {f : ι -> 理想 R} {P : 理想 R} (hp : 是素 P)
  证明: ⟨fun h => hp.prod_le.1 prod_le_inf.trans h, fun ⟨_, his, hip⟩ => (Finset.inf_le his).trans hip⟩

Depends on / 依赖: Finset, Finset.inf_le, hp.prod_le, inf_le, prod_le, prod_le_inf, prod_le_inf.trans
-/
theorem IsPrime.inf_le' {s : Finset ι} {f : ι -> Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.inf f <= P ↔ exists i in s, f i <= P :=
⟨fun h => hp.prod_le.1 prod_le_inf.trans h, fun ⟨_, his, hip⟩ => (Finset.inf_le his).trans hip⟩

/--
theorem `eq_inf_of_isPrime_inf` / 定理 `eq_inf_of_isPrime_inf`

English:
theorem eq_inf_of_isPrime_inf
  given: {s : Finset ι} {f : ι -> Ideal R} (hp : IsPrime (s.inf f))
  proof: (hp.inf_le'.mp le_rfl).imp (fun _ ⟨h1, h2⟩ => ⟨h1, le_antisymm h2 (Finset.inf_le h1)⟩)

中文:
定理 eq_inf_of_isPrime_inf
  条件: {s : 有限集 ι} {f : ι -> 理想 R} (hp : 是素 (s.下确界 f))
  证明: (hp.inf_le'.mp le_rfl).imp (fun _ ⟨h1, h2⟩ => ⟨h1, le_antisymm h2 (Finset.inf_le h1)⟩)

Depends on / 依赖: Finset, Finset.inf_le, hp.inf_le, inf_le, le_antisymm, le_rfl
-/
theorem eq_inf_of_isPrime_inf {s : Finset ι} {f : ι -> Ideal R} (hp : IsPrime (s.inf f)) :
    exists i in s, f i = s.inf f :=
  (hp.inf_le'.mp le_rfl).imp (fun _ ⟨h1, h2⟩ => ⟨h1, le_antisymm h2 (Finset.inf_le h1)⟩)

/--
theorem `IsPrime.notMem_of_isCoprime_of_mem` / 定理 `IsPrime.notMem_of_isCoprime_of_mem`

English:
theorem IsPrime.notMem_of_isCoprime_of_mem
  statement: {I : Ideal R} [I.IsPrime] {x y : R} (h : IsCoprime x y)
  proof: fun hy =>
  have ⟨a, b, e⟩ := h
  Ideal.IsPrime.one_notMem ‹_› (e ▸ I.add_mem (I.mul_mem_left a hx) (I.mul_mem_left b hy))

中文:
定理 是素.notMem_of_isCoprime_of_mem
  结论: {I : 理想 R} [I.是素] {x y : R} (h : IsCoprime x y)
  证明: fun hy =>
  have ⟨a, b, e⟩ := h
  Ideal.IsPrime.one_notMem ‹_› (e ▸ I.add_mem (I.mul_mem_left a hx) (I.mul_mem_left b hy))
-/
theorem IsPrime.notMem_of_isCoprime_of_mem {I : Ideal R} [I.IsPrime] {x y : R} (h : IsCoprime x y)
    (hx : x in I) : y ∉ I := fun hy =>
  have ⟨a, b, e⟩ := h
  Ideal.IsPrime.one_notMem ‹_› (e ▸ I.add_mem (I.mul_mem_left a hx) (I.mul_mem_left b hy))

/--
theorem `subset_union` / 定理 `subset_union`

English:
theorem subset_union
  given: {R : Type u} [Ring R] {I J K : Ideal R}
  proof: AddSubgroupClass.subset_union

中文:
定理 subset_union
  条件: {R : 类型u} [环 R] {I J K : 理想 R}
  证明: AddSubgroupClass.subset_union

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.subset_union, subset_union
-/
theorem subset_union {R : Type u} [Ring R] {I J K : Ideal R} :
    (I : Set R) subseteq J union K ↔ I <= J ∨ I <= K :=
  AddSubgroupClass.subset_union

/--
theorem `subset_union_prime'` / 定理 `subset_union_prime'`

English:
theorem subset_union_prime'
  statement: {R : Type u} [CommRing R] {s : Finset ι} {f : ι -> Ideal R} {a b : ι}
  proof: by
  suffices
    ((I : Set R) subseteq f a union f b union ⋃ i in (↑s : Set ι), f i) -> I <= f a ∨ I <= f b ∨ exists i in s, I <= f i from
    ⟨this, fun h =>
      Or.casesOn h
        (fun h =>
Set.Subset.trans h
            Set.Subset.trans Set.subset_union_left Set.subset_union_left)
        fu

中文:
定理 subset_union_prime'
  结论: {R : 类型u} [交换环 R] {s : 有限集 ι} {f : ι -> 理想 R} {a b : ι}
  证明: by
  suffices
    ((I : Set R) subseteq f a union f b union ⋃ i in (↑s : Set ι), f i) -> I <= f a ∨ I <= f b ∨ exists i in s, I <= f i from
    ⟨this, fun h =>
      Or.casesOn h
        (fun h =>
Set.Subset.trans h
            Set.Subset.trans Set.subset_union_left Set.subset_union_left)
        fu

Depends on / 依赖: Or.casesOn, Set.Subset.trans, Set.subset_biUnion_of_mem, Set.subset_union_left, Set.subset_union_right, Subset, casesOn, subset_biUnion_of_mem, subset_union_left, subset_union_right, subseteq
-/
theorem subset_union_prime' {R : Type u} [CommRing R] {s : Finset ι} {f : ι -> Ideal R} {a b : ι}
    (hp : forall i in s, IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) subseteq f a union f b union ⋃ i in (↑s : Set ι), f i) ↔ I <= f a ∨ I <= f b ∨ exists i in s, I <= f i := by
  suffices
    ((I : Set R) subseteq f a union f b union ⋃ i in (↑s : Set ι), f i) -> I <= f a ∨ I <= f b ∨ exists i in s, I <= f i from
    ⟨this, fun h =>
      Or.casesOn h
        (fun h =>
Set.Subset.trans h
            Set.Subset.trans Set.subset_union_left Set.subset_union_left)
        fun h =>
        Or.casesOn h
          (fun h =>
Set.Subset.trans h
              Set.Subset.trans Set.subset_union_right Set.subset_union_left)
          fun ⟨i, his, hi⟩ => by
refine Set.Subset.trans hi Set.Subset.trans ?_ Set.subset_union_right
          exact Set.subset_biUnion_of_mem (u := fun x => (f x : Set R)) (Finset.mem_coe.2 his)⟩
  generalize hn : s.card = n; intro h
  induction n generalizing a b s with
  | zero =>
    clear hp
    rw [Finset.card_eq_zero] at hn
    subst hn
    rw [Finset.coe_empty]; rw [Set.biUnion_empty]; rw [Set.union_empty]; rw [subset_union] at h
    simpa only [exists_prop, Finset.notMem_empty, false_and, exists_false, or_false]
  | succ n ih =>
    classical
    replace hn : exists (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n :=
      Finset.card_eq_succ.1 hn
    rcases hn with ⟨i, t, hit, rfl, hn⟩
    replace hp : IsPrime (f i) ∧ forall x in t, IsPrime (f x) := (t.forall_mem_insert _ _).1 hp
    by_cases Ht : exists j in t, f j <= f i
    · obtain ⟨j, hjt, hfji⟩ : exists j in t, f j <= f i := Ht
      obtain ⟨u, hju, rfl⟩ : exists u, j ∉ u ∧ insert j u = t :=
        ⟨t.erase j, t.notMem_erase j, Finset.insert_erase hjt⟩
      have hp' : forall k in insert i u, IsPrime (f k) := by
        rw [Finset.forall_mem_insert] at hp ⊢
        exact ⟨hp.1, hp.2.2⟩
      have hiu : i ∉ u := mt Finset.mem_insert_of_mem hit
      have hn' : (insert i u).card = n := by
        rwa [Finset.card_insert_of_notMem] at hn ⊢
        exacts [hiu, hju]
      have h' : (I : Set R) subseteq f a union f b union ⋃ k in (↑(insert i u) : Set ι), f k := by
        rw [Finset.coe_insert] at h ⊢
        rw [Finset.coe_insert] at h
        simp only [Set.biUnion_insert] at h ⊢
        rw [← Set.union_assoc (f i : Set R)]; rw [Set.union_eq_self_of_subset_right hfji] at h
        exact h
      specialize ih hp' hn' h'
      refine ih.imp id (Or.imp id (Exists.imp fun k => ?_))
      exact And.imp (fun hk => Finset.insert_subset_insert i (Finset.subset_insert j u) hk) id
    by_cases Ha : f a <= f i
    · have h' : (I : Set R) subseteq f i union f b union ⋃ j in (↑t : Set ι), f j := by
        rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [← Set.union_assoc]; rw [Set.union_right_comm (f a : Set R)]; rw [Set.union_eq_self_of_subset_left Ha] at h
        exact h
      specialize ih hp.2 hn h'
      right
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩
      · exact Or.inl ih
      · exact Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    by_cases Hb : f b <= f i
    · have h' : (I : Set R) subseteq f a union f i union ⋃ j in (↑t : Set ι), f j := by
        rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [← Set.union_assoc]; rw [Set.union_assoc (f a : Set R)]; rw [Set.union_eq_self_of_subset_left Hb] at h
        exact h
      specialize ih hp.2 hn h'
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inl ih
      · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩)
      · exact Or.inr (Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩)
    by_cases Hi : I <= f i
    · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, Hi⟩)
    have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f <= f i := by
      simp only [hp.1.inf_le, hp.1.inf_le', not_or]
      exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩
    rcases Set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩
    by_cases HI : (I : Set R) subseteq f a union f b union ⋃ j in (↑t : Set ι), f j
    · specialize ih hp.2 hn HI
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · order
      · order
      · right
        right
        exact ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    exfalso
    rcases Set.not_subset.1 HI with ⟨s, hsI, hs⟩
    rw [Finset.coe_insert]; rw [Set.biUnion_insert] at h
    have hsi : s in f i := ((h hsI).resolve_left (mt Or.inl hs)).resolve_right (mt Or.inr hs)
    rcases h (I.add_mem hrI hsI) with (⟨ha | hb⟩ | hi | ht)
    · exact hs (Or.inl <| Or.inl <| add_sub_cancel_left r s ▸ (f a).sub_mem ha hra)
    · exact hs (Or.inl <| Or.inr <| add_sub_cancel_left r s ▸ (f b).sub_mem hb hrb)
    · exact hri (add_sub_cancel_right r s ▸ (f i).sub_mem hi hsi)
    · rw [Set.mem_iUnion₂] at ht
      rcases ht with ⟨j, hjt, hj⟩
      simp only [Finset.inf_eq_iInf, SetLike.mem_coe, Submodule.mem_iInf] at hr
exact hs Or.inr Set.mem_biUnion hjt
add_sub_cancel_left r s ▸ (f j).sub_mem hj hr j hjt

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Matsumura Ex.1.6. -/
@[stacks 00DS]
/--
theorem `subset_union_prime` / 定理 `subset_union_prime`

English:
theorem subset_union_prime
  statement: {R : Type u} [CommRing R] {s : Finset ι} {f : ι -> Ideal R} (a b : ι)
  proof: suffices ((I : Set R) subseteq ⋃ i in (↑s : Set ι), f i) -> exists i, i in s ∧ I <= f i by
    have aux := fun h => (bex_def.2 <| this h)
    simp_rw [exists_prop] at aux
    refine ⟨aux, fun ⟨i, his, hi⟩ => Set.Subset.trans hi ?_⟩
    apply Set.subset_biUnion_of_mem (show i in (↑s : Set ι) from his

中文:
定理 subset_union_prime
  结论: {R : 类型u} [交换环 R] {s : 有限集 ι} {f : ι -> 理想 R} (a b : ι)
  证明: suffices ((I : Set R) subseteq ⋃ i in (↑s : Set ι), f i) -> exists i, i in s ∧ I <= f i by
    have aux := fun h => (bex_def.2 <| this h)
    simp_rw [exists_prop] at aux
    refine ⟨aux, fun ⟨i, his, hi⟩ => Set.Subset.trans hi ?_⟩
    apply Set.subset_biUnion_of_mem (show i in (↑s : Set ι) from his

Depends on / 依赖: Finset, Finset.insert_erase, Finset.notMem_erase, Set.Subset.trans, Set.subset_biUnion_of_mem, Subset, bex_def, classical, exists_prop, insert, insert_erase, notMem_erase, s.erase, simp_rw, subset_biUnion_of_mem, subseteq
-/
theorem subset_union_prime {R : Type u} [CommRing R] {s : Finset ι} {f : ι -> Ideal R} (a b : ι)
    (hp : forall i in s, i != a -> i != b -> IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) subseteq ⋃ i in (↑s : Set ι), f i) ↔ exists i in s, I <= f i :=
  suffices ((I : Set R) subseteq ⋃ i in (↑s : Set ι), f i) -> exists i, i in s ∧ I <= f i by
    have aux := fun h => (bex_def.2 <| this h)
    simp_rw [exists_prop] at aux
    refine ⟨aux, fun ⟨i, his, hi⟩ => Set.Subset.trans hi ?_⟩
    apply Set.subset_biUnion_of_mem (show i in (↑s : Set ι) from his)
  fun h : (I : Set R) subseteq ⋃ i in (↑s : Set ι), f i => by
  classical
    by_cases has : a in s
    · obtain ⟨t, hat, rfl⟩ : exists t, a ∉ t ∧ insert a t = s :=
        ⟨s.erase a, Finset.notMem_erase a s, Finset.insert_erase has⟩
      by_cases hbt : b in t
      · obtain ⟨u, hbu, rfl⟩ : exists u, b ∉ u ∧ insert b u = t :=
          ⟨t.erase b, Finset.notMem_erase b t, Finset.insert_erase hbt⟩
        have hp' : forall i in u, IsPrime (f i) := by
          intro i hiu
          refine hp i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiu)) ?_ ?_ <;>
              rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert]; rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [Set.biUnion_insert]; rw [←
          Set.union_assoc]; rw [subset_union_prime' hp'] at h
        rwa [Finset.exists_mem_insert, Finset.exists_mem_insert]
      · have hp' : forall j in t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [← Set.union_self (f a : Set R)]; rw [subset_union_prime' hp']; rw [← or_assoc]; rw [or_self_iff] at h
        rwa [Finset.exists_mem_insert]
    · by_cases hbs : b in s
      · obtain ⟨t, hbt, rfl⟩ : exists t, b ∉ t ∧ insert b t = s :=
          ⟨s.erase b, Finset.notMem_erase b s, Finset.insert_erase hbs⟩
        have hp' : forall j in t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [← Set.union_self (f b : Set R)]; rw [subset_union_prime' hp']; rw [← or_assoc]; rw [or_self_iff] at h
        rwa [Finset.exists_mem_insert]
      rcases s.eq_empty_or_nonempty with rfl | hsne
      · rw [Finset.coe_empty, Set.biUnion_empty] at h
        exact (h I.zero_mem).elim
      · obtain ⟨i, his⟩ := hsne
        obtain ⟨t, _, rfl⟩ : exists t, i ∉ t ∧ insert i t = s :=
          ⟨s.erase i, Finset.notMem_erase i s, Finset.insert_erase his⟩
        have hp' : forall j in t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert]; rw [Set.biUnion_insert]; rw [← Set.union_self (f i : Set R)]; rw [subset_union_prime' hp']; rw [← or_assoc]; rw [or_self_iff] at h
        rwa [Finset.exists_mem_insert]

/--
lemma `subset_union_prime_finite` / 引理 `subset_union_prime_finite`

English:
lemma subset_union_prime_finite
  statement: {R ι : Type*} [CommRing R] {s : Set ι}
  proof: by
  rcases Set.Finite.exists_finset hs with ⟨t, ht⟩
  have heq : ⋃ i in s, f i = ⋃ i in t, (f i : Set R) := by
    ext
    simpa using exists_congr (fun i => (and_congr_left fun a => ht i).symm)
  have hmem_union : ((I : Set R) subseteq ⋃ i in s, f i) ↔ ((I : Set R) subseteq ⋃ i in (t : Set ι), f i

中文:
引理 subset_union_prime_finite
  结论: {R ι : 类型} [交换环 R] {s : 集合 ι}
  证明: by
  rcases Set.Finite.exists_finset hs with ⟨t, ht⟩
  have heq : ⋃ i in s, f i = ⋃ i in t, (f i : Set R) := by
    ext
    simpa using exists_congr (fun i => (and_congr_left fun a => ht i).symm)
  have hmem_union : ((I : Set R) subseteq ⋃ i in s, f i) ↔ ((I : Set R) subseteq ⋃ i in (t : Set ι), f i

Depends on / 依赖: Finite, Ideal.subset_union_prime, Set.Finite.exists_finset, and_congr_left, exists_congr, exists_finset, hmem_union, subset_union_prime, subseteq, to_iff
-/
lemma subset_union_prime_finite {R ι : Type*} [CommRing R] {s : Set ι}
    (hs : s.Finite) {f : ι -> Ideal R} (a b : ι)
    (hp : forall i in s, i != a -> i != b -> (f i).IsPrime) {I : Ideal R} :
    ((I : Set R) subseteq ⋃ i in s, f i) ↔ exists i in s, I <= f i := by
  rcases Set.Finite.exists_finset hs with ⟨t, ht⟩
  have heq : ⋃ i in s, f i = ⋃ i in t, (f i : Set R) := by
    ext
    simpa using exists_congr (fun i => (and_congr_left fun a => ht i).symm)
  have hmem_union : ((I : Set R) subseteq ⋃ i in s, f i) ↔ ((I : Set R) subseteq ⋃ i in (t : Set ι), f i) :=
    (congrArg _ heq).to_iff
  rw [hmem_union]; rw [Ideal.subset_union_prime a b (fun i hin => hp i ((ht i).mp hin))]
  exact exists_congr (fun i => and_congr_left fun _ => ht i)

/--
lemma `subset_iUnion_iff_mem_of_isMaximal_of_finite` / 引理 `subset_iUnion_iff_mem_of_isMaximal_of_finite`

English:
lemma subset_iUnion_iff_mem_of_isMaximal_of_finite
  proof: by
  refine (subset_union_prime_finite hs a b hp).trans ⟨fun ⟨I, mem, le⟩ => ?_, (⟨M, ·, le_rfl⟩)⟩
  rwa [‹M.IsMaximal›.eq_of_le _ le]
  simp_rw [← or_iff_not_imp_left] at hp
  obtain rfl | rfl | hp := hp I mem
  exacts [ha, hb, hp.ne_top]

中文:
引理 subset_iUnion_iff_mem_of_isMaximal_of_finite
  证明: by
  refine (subset_union_prime_finite hs a b hp).trans ⟨fun ⟨I, mem, le⟩ => ?_, (⟨M, ·, le_rfl⟩)⟩
  rwa [‹M.IsMaximal›.eq_of_le _ le]
  simp_rw [← or_iff_not_imp_left] at hp
  obtain rfl | rfl | hp := hp I mem
  exacts [ha, hb, hp.ne_top]

Depends on / 依赖: IsMaximal, M.IsMaximal, eq_of_le, exacts, hp.ne_top, le_rfl, ne_top, or_iff_not_imp_left, simp_rw, subset_union_prime_finite
-/
lemma subset_iUnion_iff_mem_of_isMaximal_of_finite
    {R : Type*} [CommRing R] {M : Ideal R} [M.IsMaximal] {S : Set (Ideal R)}
    (hs : S.Finite) (a b : Ideal R) (hp : forall I in S, I != a -> I != b -> I.IsPrime)
    (ha : a != ⊤) (hb : b != ⊤) : ((M : Set R) subseteq ⋃ I in S, I) ↔ M in S := by
  refine (subset_union_prime_finite hs a b hp).trans ⟨fun ⟨I, mem, le⟩ => ?_, (⟨M, ·, le_rfl⟩)⟩
  rwa [‹M.IsMaximal›.eq_of_le _ le]
  simp_rw [← or_iff_not_imp_left] at hp
  obtain rfl | rfl | hp := hp I mem
  exacts [ha, hb, hp.ne_top]

/--
theorem `IsMaximal.exists_inv_pow` / 定理 `IsMaximal.exists_inv_pow`

English:
theorem IsMaximal.exists_inv_pow
  statement: (I : Ideal R) [I.IsMaximal]
  proof: by
  obtain ⟨y, i, hmem, hi⟩ := Ideal.IsMaximal.exists_inv ‹_› hx
  obtain ⟨y, hy⟩ : exists y : R, y * x + i ^ n = 1 := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z * i + y, ?_⟩
      trans z * i * x + i * i ^ n + y * x
      

中文:
定理 是极大.存在_inv_pow
  结论: (I : 理想 R) [I.是极大]
  证明: by
  obtain ⟨y, i, hmem, hi⟩ := Ideal.IsMaximal.exists_inv ‹_› hx
  obtain ⟨y, hy⟩ : exists y : R, y * x + i ^ n = 1 := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z * i + y, ?_⟩
      trans z * i * x + i * i ^ n + y * x
      

Depends on / 依赖: Ideal.IsMaximal.exists_inv, Ideal.pow_mem_pow, IsMaximal, add_comm, exists_inv, mul_add, mul_assoc, mul_comm, pow_mem_pow
-/
theorem IsMaximal.exists_inv_pow (I : Ideal R) [I.IsMaximal]
    {x : R} (hx : x ∉ I) (n : Nat) : exists (y : R), exists i in I ^ n, y * x + i = 1 := by
  obtain ⟨y, i, hmem, hi⟩ := Ideal.IsMaximal.exists_inv ‹_› hx
  obtain ⟨y, hy⟩ : exists y : R, y * x + i ^ n = 1 := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z * i + y, ?_⟩
      trans z * i * x + i * i ^ n + y * x
      · ring
      · rw [mul_comm z i, mul_assoc, ← mul_add, hz, add_comm]
        simpa
  exact ⟨y, i ^ n, Ideal.pow_mem_pow hmem n, hy⟩

/--
theorem `IsMaximal.mul_mem_pow` / 定理 `IsMaximal.mul_mem_pow`

English:
theorem IsMaximal.mul_mem_pow
  statement: (I : Ideal R) [I.IsMaximal]
  proof: by
  rw [Classical.or_iff_not_imp_left]
  intro ha
  obtain ⟨c, i, hi, hc⟩ := exists_inv_pow I ha n
  obtain hb := congr($hc * b)
  rw [one_mul] at hb
  rw [← hb]; rw [add_mul]; rw [mul_assoc]
  exact add_mem (mul_mem_left _ _ h) (mul_mem_right _ _ hi)

中文:
定理 是极大.mul_mem_pow
  结论: (I : 理想 R) [I.是极大]
  证明: by
  rw [Classical.or_iff_not_imp_left]
  intro ha
  obtain ⟨c, i, hi, hc⟩ := exists_inv_pow I ha n
  obtain hb := congr($hc * b)
  rw [one_mul] at hb
  rw [← hb]; rw [add_mul]; rw [mul_assoc]
  exact add_mem (mul_mem_left _ _ h) (mul_mem_right _ _ hi)

Depends on / 依赖: Classical, Classical.or_iff_not_imp_left, add_mem, add_mul, exists_inv_pow, mul_assoc, mul_mem_left, mul_mem_right, one_mul, or_iff_not_imp_left
-/
theorem IsMaximal.mul_mem_pow (I : Ideal R) [I.IsMaximal]
    {a b : R} {n : Nat} (h : a * b in I ^ n) : a in I ∨ b in I ^ n := by
  rw [Classical.or_iff_not_imp_left]
  intro ha
  obtain ⟨c, i, hi, hc⟩ := exists_inv_pow I ha n
  obtain hb := congr($hc * b)
  rw [one_mul] at hb
  rw [← hb]; rw [add_mul]; rw [mul_assoc]
  exact add_mem (mul_mem_left _ _ h) (mul_mem_right _ _ hi)

/--
theorem `IsMaximal.mem_pow_mul` / 定理 `IsMaximal.mem_pow_mul`

English:
theorem IsMaximal.mem_pow_mul
  statement: {R : Type*} [CommSemiring R] (I : Ideal R) [I.IsMaximal]
  proof: by
  rw [mul_comm] at h
  rw [or_comm]
  exact mul_mem_pow _ h

中文:
定理 是极大.mem_pow_mul
  结论: {R : 类型} [交换半环 R] (I : 理想 R) [I.是极大]
  证明: by
  rw [mul_comm] at h
  rw [or_comm]
  exact mul_mem_pow _ h

Depends on / 依赖: mul_comm, mul_mem_pow, or_comm
-/
theorem IsMaximal.mem_pow_mul {R : Type*} [CommSemiring R] (I : Ideal R) [I.IsMaximal]
    {a b : R} {n : Nat} (h : a * b in I ^ n) : a in I ^ n ∨ b in I := by
  rw [mul_comm] at h
  rw [or_comm]
  exact mul_mem_pow _ h

section Dvd

/--
theorem `le_of_dvd` / 定理 `le_of_dvd`

English:
theorem le_of_dvd
  given: {I J : Ideal R}
  statement: I ∣ J -> J <= I

中文:
定理 le_of_dvd
  条件: {I J : 理想 R}
  结论: I ∣ J -> J <= I
-/
theorem le_of_dvd {I J : Ideal R} : I ∣ J -> J <= I
  | ⟨_, h⟩ => h.symm ▸ le_trans mul_le_inf inf_le_left

@[simp]
/--
theorem `dvd_bot` / 定理 `dvd_bot`

English:
theorem dvd_bot
  given: {I : Ideal R}
  statement: I ∣ ⊥
  proof: dvd_zero I

中文:
定理 dvd_bot
  条件: {I : 理想 R}
  结论: I ∣ ⊥
  证明: dvd_zero I

Depends on / 依赖: dvd_zero
-/
theorem dvd_bot {I : Ideal R} : I ∣ ⊥ :=
  dvd_zero I

/-- See also `isUnit_iff_eq_one`. -/
@[simp high]
/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  given: {I : Ideal R}
  statement: IsUnit I ↔ I = ⊤
  proof: isUnit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h => ⟨⊤, by rw [mul_top, h]⟩⟩)

中文:
定理 isUnit_iff
  条件: {I : 理想 R}
  结论: 是单位 I ↔ I = ⊤
  证明: isUnit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h => ⟨⊤, by rw [mul_top, h]⟩⟩)

Depends on / 依赖: Ideal.le_of_dvd, eq_top_iff, eq_top_iff.mpr, isUnit_iff_dvd_one, isUnit_iff_dvd_one.trans, le_of_dvd, mul_top, one_eq_top
-/
theorem isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤ :=
  isUnit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h => ⟨⊤, by rw [mul_top, h]⟩⟩)

/--
Instance `uniqueUnits` / 实例 `uniqueUnits`

English:
instance uniqueUnits
  signature: : Unique (Ideal R)ˣ where
  body: 1
  uniq u := Units.ext (show (u : Ideal R) = 1 by rw [isUnit_iff.mp u.isUnit, one_eq_top])

中文:
实例 uniqueUnits
  签名: : 唯一 (理想 R)ˣ where
  定义体: 1
  uniq u := Units.ext (show (u : Ideal R) = 1 by rw [isUnit_iff.mp u.isUnit, one_eq_top])
-/
instance uniqueUnits : Unique (Ideal R)ˣ where
  default := 1
  uniq u := Units.ext (show (u : Ideal R) = 1 by rw [isUnit_iff.mp u.isUnit, one_eq_top])

end Dvd

end MulAndRadical



section Total

variable (ι : Type*)
variable (M : Type*) [AddCommGroup M] {R : Type*} [CommRing R] [Module R M] (I : Ideal R)
variable (v : ι -> M) (hv : Submodule.span R (Set.range v) = ⊤)

/--
Definition of `finsuppTotal` / `finsuppTotal` 的定义

English:
definition finsuppTotal
  signature: : (ι ->₀ I) ->ₗ[R] M
  body: (Finsupp.linearCombination R v).comp (Finsupp.mapRange.linearMap I.subtype)

中文:
定义 finsuppTotal
  签名: : (ι ->₀ I) ->ₗ[R] M
  定义体: (Finsupp.linearCombination R v).comp (Finsupp.mapRange.linearMap I.subtype)

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.mapRange.linearMap, I.subtype, linearCombination, linearMap, mapRange, subtype
-/
noncomputable def finsuppTotal : (ι ->₀ I) ->ₗ[R] M :=
  (Finsupp.linearCombination R v).comp (Finsupp.mapRange.linearMap I.subtype)

variable {ι M v}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `finsuppTotal_apply` / 定理 `finsuppTotal_apply`

English:
theorem finsuppTotal_apply
  given: (f : ι ->₀ I)
  proof: by
  dsimp [finsuppTotal]
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_mapRange_index]
  exact fun _ => zero_smul _ _

中文:
定理 finsuppTotal_apply
  条件: (f : ι ->₀ I)
  证明: by
  dsimp [finsuppTotal]
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_mapRange_index]
  exact fun _ => zero_smul _ _

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index, finsuppTotal, linearCombination_apply, sum_mapRange_index, zero_smul
-/
theorem finsuppTotal_apply (f : ι ->₀ I) :
    finsuppTotal ι M I v f = f.sum fun i x => (x : R) • v i := by
  dsimp [finsuppTotal]
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_mapRange_index]
  exact fun _ => zero_smul _ _

/--
theorem `finsuppTotal_apply_eq_of_fintype` / 定理 `finsuppTotal_apply_eq_of_fintype`

English:
theorem finsuppTotal_apply_eq_of_fintype
  given: [Fintype ι] (f : ι ->₀ I)
  proof: by
  rw [finsuppTotal_apply]; rw [Finsupp.sum_fintype]
  exact fun _ => zero_smul _ _

中文:
定理 finsuppTotal_apply_eq_of_fintype
  条件: [有限类型 ι] (f : ι ->₀ I)
  证明: by
  rw [finsuppTotal_apply]; rw [Finsupp.sum_fintype]
  exact fun _ => zero_smul _ _

Depends on / 依赖: Finsupp, Finsupp.sum_fintype, finsuppTotal_apply, sum_fintype, zero_smul
-/
theorem finsuppTotal_apply_eq_of_fintype [Fintype ι] (f : ι ->₀ I) :
    finsuppTotal ι M I v f = ∑ i, (f i : R) • v i := by
  rw [finsuppTotal_apply]; rw [Finsupp.sum_fintype]
  exact fun _ => zero_smul _ _

/--
theorem `range_finsuppTotal` / 定理 `range_finsuppTotal`

English:
theorem range_finsuppTotal
  proof: by
  ext
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum]
  refine ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine ⟨a.mapRange (fun r => if h : r in I then ⟨r, h⟩ else 0)
      (by simp only [Submodule.zero_mem, ↓reduc

中文:
定理 range_finsuppTotal
  证明: by
  ext
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum]
  refine ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine ⟨a.mapRange (fun r => if h : r in I then ⟨r, h⟩ else 0)
      (by simp only [Submodule.zero_mem, ↓reduc

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearMap, Finsupp.sum_congr, Finsupp.sum_mapRange_index, I.subtype, Submodule, Submodule.mem_ideal_smul_span_iff_exists_sum, Submodule.zero_mem, a.mapRange, classical, dif_pos, finsuppTotal_apply, linearMap, mapRange, mem_ideal_smul_span_iff_exists_sum, reduceDIte, subtype, sum_congr, sum_mapRange_index, zero_mem
-/
theorem range_finsuppTotal :
    LinearMap.range (finsuppTotal ι M I v) = I • Submodule.span R (Set.range v) := by
  ext
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum]
  refine ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine ⟨a.mapRange (fun r => if h : r in I then ⟨r, h⟩ else 0)
      (by simp only [Submodule.zero_mem, ↓reduceDIte]; rfl), ?_⟩
    rw [finsuppTotal_apply]; rw [Finsupp.sum_mapRange_index]
    · apply Finsupp.sum_congr
      intro i _
      rw [dif_pos (ha i)]
    · exact fun _ => zero_smul _ _

end Total


/-- `Associates (Ideal R)` almost never has decidable equality.
We add a global instance that `Associates (Ideal R)` has decidable
equality, coming from the choice axiom, so that we don't have to provide
`[DecidableEq (Associates (Ideal R))]` arguments in lemma statements. -/
noncomputable instance {R : Type*} [CommSemiring R] :
    DecidableEq (Associates (Ideal R)) :=
  Classical.typeDecidableEq _

/-- `Associates (Ideal R)` almost never has a decidable reducibility check.
We add a global instance that members of `Associates (Ideal R)` have decidable
reducibility, coming from the choice axiom, so that we don't have to provide
this as an arguments in lemma statements. -/
noncomputable instance {R : Type*} [CommSemiring R] (I : Associates (Ideal R)) :
    Decidable (Irreducible I) :=
  Classical.propDecidable _

end Ideal

section span_range
variable {α R : Type*} [Semiring R]

/--
theorem `Finsupp.mem_ideal_span_range_iff_exists_finsupp` / 定理 `Finsupp.mem_ideal_span_range_iff_exists_finsupp`

English:
theorem Finsupp.mem_ideal_span_range_iff_exists_finsupp
  given: {x : R} {v : α -> R}
  proof: Finsupp.mem_span_range_iff_exists_finsupp

中文:
定理 有限支撑.mem_ideal_span_range_iff_存在_finsupp
  条件: {x : R} {v : α -> R}
  证明: Finsupp.mem_span_range_iff_exists_finsupp

Depends on / 依赖: Finsupp, Finsupp.mem_span_range_iff_exists_finsupp, mem_span_range_iff_exists_finsupp
-/
theorem Finsupp.mem_ideal_span_range_iff_exists_finsupp {x : R} {v : α -> R} :
    x in Ideal.span (Set.range v) ↔ exists c : α ->₀ R, (c.sum fun i a => a * v i) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp

/--
theorem `Ideal.mem_span_range_iff_exists_fun` / 定理 `Ideal.mem_span_range_iff_exists_fun`

English:
theorem Ideal.mem_span_range_iff_exists_fun
  given: [Fintype α] {x : R} {v : α -> R}
  proof: Submodule.mem_span_range_iff_exists_fun _

中文:
定理 理想.mem_span_range_iff_存在_fun
  条件: [有限类型 α] {x : R} {v : α -> R}
  证明: Submodule.mem_span_range_iff_exists_fun _

Depends on / 依赖: Submodule, Submodule.mem_span_range_iff_exists_fun, mem_span_range_iff_exists_fun
-/
theorem Ideal.mem_span_range_iff_exists_fun [Fintype α] {x : R} {v : α -> R} :
    x in Ideal.span (Set.range v) ↔ exists c : α -> R, ∑ i, c i * v i = x :=
  Submodule.mem_span_range_iff_exists_fun _

end span_range

/--
theorem `Associates.mk_ne_zero'` / 定理 `Associates.mk_ne_zero'`

English:
theorem Associates.mk_ne_zero'
  given: {R : Type*} [CommSemiring R] {r : R}
  proof: by
  rw [Associates.mk_ne_zero]; rw [Ideal.zero_eq_bot]; rw [Ne]; rw [Ideal.span_singleton_eq_bot]

中文:
定理 Associates.mk_ne_zero'
  条件: {R : 类型} [交换半环 R] {r : R}
  证明: by
  rw [Associates.mk_ne_zero]; rw [Ideal.zero_eq_bot]; rw [Ne]; rw [Ideal.span_singleton_eq_bot]

Depends on / 依赖: Associates, Associates.mk_ne_zero, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, mk_ne_zero, span_singleton_eq_bot, zero_eq_bot
-/
theorem Associates.mk_ne_zero' {R : Type*} [CommSemiring R] {r : R} :
    Associates.mk (Ideal.span {r} : Ideal R) != 0 ↔ r != 0 := by
  rw [Associates.mk_ne_zero]; rw [Ideal.zero_eq_bot]; rw [Ne]; rw [Ideal.span_singleton_eq_bot]

open scoped nonZeroDivisors in
/--
theorem `Ideal.span_singleton_nonZeroDivisors` / 定理 `Ideal.span_singleton_nonZeroDivisors`

English:
theorem Ideal.span_singleton_nonZeroDivisors
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R]
  proof: by
  cases subsingleton_or_nontrivial R
  · simp_rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    exact ⟨fun _ _ _ => Subsingleton.eq_zero _, fun _ _ _ => Subsingleton.eq_zero _⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero, ne_eq, zero_eq_bot,
      span_singleton_eq_b

中文:
定理 理想.span_singleton_nonZeroDivisors
  结论: {R : 类型} [交换半环 R] [无零因子 R]
  证明: by
  cases subsingleton_or_nontrivial R
  · simp_rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    exact ⟨fun _ _ _ => Subsingleton.eq_zero _, fun _ _ _ => Subsingleton.eq_zero _⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero, ne_eq, zero_eq_bot,
      span_singleton_eq_b

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, mem_nonZeroDivisors_iff_ne_zero, ne_eq, nonZeroDivisorsRight_eq_nonZeroDivisors, simp_rw, span_singleton_eq_bot, subsingleton_or_nontrivial, zero_eq_bot
-/
theorem Ideal.span_singleton_nonZeroDivisors {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {r : R} : span {r} in (Ideal R)⁰ ↔ r in R⁰ := by
  cases subsingleton_or_nontrivial R
  · simp_rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    exact ⟨fun _ _ _ => Subsingleton.eq_zero _, fun _ _ _ => Subsingleton.eq_zero _⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero, ne_eq, zero_eq_bot,
      span_singleton_eq_bot]

/--
theorem `Ideal.primeCompl_le_nonZeroDivisors` / 定理 `Ideal.primeCompl_le_nonZeroDivisors`

English:
theorem Ideal.primeCompl_le_nonZeroDivisors
  statement: {R : Type*} [CommSemiring R] [NoZeroDivisors R]
  proof: le_nonZeroDivisors_of_noZeroDivisors not_not_intro P.zero_mem

中文:
定理 理想.primeCompl_le_nonZeroDivisors
  结论: {R : 类型} [交换半环 R] [无零因子 R]
  证明: le_nonZeroDivisors_of_noZeroDivisors not_not_intro P.zero_mem

Depends on / 依赖: P.zero_mem, le_nonZeroDivisors_of_noZeroDivisors, not_not_intro, zero_mem
-/
theorem Ideal.primeCompl_le_nonZeroDivisors {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (P : Ideal R) [P.IsPrime] : P.primeCompl <= nonZeroDivisors R :=
le_nonZeroDivisors_of_noZeroDivisors not_not_intro P.zero_mem

namespace Submodule

variable {R : Type*}

section

variable [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/--
Instance `moduleSubmodule` / 实例 `moduleSubmodule`

English:
instance moduleSubmodule
  signature: : Module (Ideal R) (Submodule R M) where
  body: smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.mul_smul
  one_smul := by simp
  zero_smul := bot_smul
  smul_zero := smul_bot

中文:
实例 moduleSubmodule
  签名: : 模 (理想 R) (子模 R M) where
  定义体: smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.mul_smul
  one_smul := by simp
  zero_smul := bot_smul
  smul_zero := smul_bot

Depends on / 依赖: smul_sup
-/
instance moduleSubmodule : Module (Ideal R) (Submodule R M) where
  smul_add := smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.mul_smul
  one_smul := by simp
  zero_smul := bot_smul
  smul_zero := smul_bot

/--
lemma `span_smul_eq` / 引理 `span_smul_eq`

English:
lemma span_smul_eq
  proof: by
  rw [← coe_set_smul]; rw [coe_span_smul]

@[simp]

中文:
引理 span_smul_eq
  证明: by
  rw [← coe_set_smul]; rw [coe_span_smul]

@[simp]

Depends on / 依赖: coe_set_smul, coe_span_smul
-/
lemma span_smul_eq
    (s : Set R) (N : Submodule R M) :
    Ideal.span s • N = s • N := by
  rw [← coe_set_smul]; rw [coe_span_smul]

@[simp]
/--
theorem `set_smul_top_eq_span` / 定理 `set_smul_top_eq_span`

English:
theorem set_smul_top_eq_span
  given: (s : Set R)
  proof: (span_smul_eq s ⊤).symm.trans (Ideal.span s).mul_top

中文:
定理 set_smul_top_eq_span
  条件: (s : 集合 R)
  证明: (span_smul_eq s ⊤).symm.trans (Ideal.span s).mul_top

Depends on / 依赖: Ideal.span, mul_top, span_smul_eq, symm.trans
-/
theorem set_smul_top_eq_span (s : Set R) :
    s • ⊤ = Ideal.span s :=
  (span_smul_eq s ⊤).symm.trans (Ideal.span s).mul_top

/--
lemma `smul_le_span` / 引理 `smul_le_span`

English:
lemma smul_le_span
  given: (s : Set R) (I : Ideal R)
  statement: s • I <= Ideal.span s
  proof: by
  simp [← Submodule.set_smul_top_eq_span, smul_le_smul_left]

中文:
引理 smul_le_span
  条件: (s : 集合 R) (I : 理想 R)
  结论: s • I <= 理想.span s
  证明: by
  simp [← Submodule.set_smul_top_eq_span, smul_le_smul_left]

Depends on / 依赖: Submodule, Submodule.set_smul_top_eq_span, set_smul_top_eq_span, smul_le_smul_left
-/
lemma smul_le_span (s : Set R) (I : Ideal R) : s • I <= Ideal.span s := by
  simp [← Submodule.set_smul_top_eq_span, smul_le_smul_left]

variable {A B} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

open Submodule

/--
Instance `algebraIdeal` / 实例 `algebraIdeal`

English:
instance algebraIdeal
  signature: : Algebra (Ideal R) (Submodule R A) where
  body: moduleSubmodule
  algebraMap :=
  { toFun := map (Algebra.linearMap R A)
    map_one' := by
      rw [one_eq_span]; rw [map_span]; rw [Set.image_singleton]; rw [Algebra.linearMap_apply]; rw [map_one]; rw [one_eq_span]
    map_mul' := (Submodule.map_mul · · <| Algebra.ofId R A)
    map_zero' := map_b

中文:
实例 algebraIdeal
  签名: : 代数 (理想 R) (子模 R A) where
  定义体: moduleSubmodule
  algebraMap :=
  { toFun := map (Algebra.linearMap R A)
    map_one' := by
      rw [one_eq_span]; rw [map_span]; rw [Set.image_singleton]; rw [Algebra.linearMap_apply]; rw [map_one]; rw [one_eq_span]
    map_mul' := (Submodule.map_mul · · <| Algebra.ofId R A)
    map_zero' := map_b

Depends on / 依赖: moduleSubmodule
-/
instance algebraIdeal : Algebra (Ideal R) (Submodule R A) where
  __ := moduleSubmodule
  algebraMap :=
  { toFun := map (Algebra.linearMap R A)
    map_one' := by
      rw [one_eq_span]; rw [map_span]; rw [Set.image_singleton]; rw [Algebra.linearMap_apply]; rw [map_one]; rw [one_eq_span]
    map_mul' := (Submodule.map_mul · · <| Algebra.ofId R A)
    map_zero' := map_bot _
    map_add' := (map_sup · · _) }
commutes' I M := mul_comm_of_commute by rintro _ ⟨r, _, rfl⟩ a _; apply Algebra.commutes
  smul_def' I M := le_antisymm (smul_le.mpr fun r hr a ha => by
rw [Algebra.smul_def]; exact Submodule.mul_mem_mul ⟨r, hr, rfl⟩ ha) (Submodule.mul_le.mpr by
    rintro _ ⟨r, hr, rfl⟩ a ha; rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr ha)

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (f : A ->ₐ[R] B)
  body: mapHom f
  commutes' I := (map_comp _ _ I).symm.trans (congr_arg (map · I) <| LinearMap.ext f.commutes)

中文:
定义 mapAlgHom
  签名: (f : A ->ₐ[R] B)
  定义体: mapHom f
  commutes' I := (map_comp _ _ I).symm.trans (congr_arg (map · I) <| LinearMap.ext f.commutes)
-/
@[simps!] def mapAlgHom (f : A ->ₐ[R] B) : Submodule R A ->ₐ[Ideal R] Submodule R B where
  __ := mapHom f
  commutes' I := (map_comp _ _ I).symm.trans (congr_arg (map · I) <| LinearMap.ext f.commutes)

-- TODO: when A, B noncommutative, still has `MulEquiv`.
/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (f : A ≃ₐ[R] B)
  body: mapAlgHom f
  invFun := mapAlgHom f.symm
left_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.left_inv ·)).trans (map_id I)
right_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.right_inv ·)).trans (map_id I)

中文:
定义 mapAlgEquiv
  签名: (f : A ≃ₐ[R] B)
  定义体: mapAlgHom f
  invFun := mapAlgHom f.symm
left_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.left_inv ·)).trans (map_id I)
right_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.right_inv ·)).trans (map_id I)
-/
@[simps!] def mapAlgEquiv (f : A ≃ₐ[R] B) : Submodule R A ≃ₐ[Ideal R] Submodule R B where
  __ := mapAlgHom f
  invFun := mapAlgHom f.symm
left_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.left_inv ·)).trans (map_id I)
right_inv I := (map_comp _ _ I).symm.trans
    (congr_arg (map · I) <| LinearMap.ext (f.right_inv ·)).trans (map_id I)

end

variable [Semiring R] {M N : Type*}

/--
lemma `smul_top_le_comap_smul_top` / 引理 `smul_top_le_comap_smul_top`

English:
lemma smul_top_le_comap_smul_top
  statement: [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  proof: map_le_iff_le_comap.mp le_of_eq_of_le (map_smul'' _ _ _)
    smul_mono_right _ le_top

中文:
引理 smul_top_le_comap_smul_top
  结论: [加法交换幺半群 M] [加法交换幺半群 N] [模 R M] [模 R N]
  证明: map_le_iff_le_comap.mp le_of_eq_of_le (map_smul'' _ _ _)
    smul_mono_right _ le_top

Depends on / 依赖: le_of_eq_of_le, le_top, map_le_iff_le_comap, map_le_iff_le_comap.mp, map_smul, smul_mono_right
-/
lemma smul_top_le_comap_smul_top [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (I : Ideal R) (f : M ->ₗ[R] N) : I • ⊤ <= comap f (I • ⊤) :=
map_le_iff_le_comap.mp le_of_eq_of_le (map_smul'' _ _ _)
    smul_mono_right _ le_top

/--
lemma `comap_smul_top_of_surjective` / 引理 `comap_smul_top_of_surjective`

English:
lemma comap_smul_top_of_surjective
  statement: [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  proof: by
  rw [← Submodule.comap_map_eq f]; rw [Submodule.map_smul'']; rw [map_top]; rw [LinearMap.range_eq_top.mpr h]

中文:
引理 comap_smul_top_of_surjective
  结论: [加法交换群 M] [加法交换群 N] [模 R M] [模 R N]
  证明: by
  rw [← Submodule.comap_map_eq f]; rw [Submodule.map_smul'']; rw [map_top]; rw [LinearMap.range_eq_top.mpr h]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, Submodule, Submodule.comap_map_eq, Submodule.map_smul, comap_map_eq, map_smul, map_top, range_eq_top
-/
lemma comap_smul_top_of_surjective [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (f : M ->ₗ[R] N) (h : Function.Surjective f) :
    comap f (I • ⊤) = I • ⊤ ⊔ (LinearMap.ker f) := by
  rw [← Submodule.comap_map_eq f]; rw [Submodule.map_smul'']; rw [map_top]; rw [LinearMap.range_eq_top.mpr h]

end Submodule

instance {R} [Semiring R] : NonUnitalSubsemiringClass (Ideal R) R where
  mul_mem _ hb := Ideal.mul_mem_left _ _ hb
instance {R} [Ring R] : NonUnitalSubringClass (Ideal R) R where

/--
lemma `Ideal.exists_subset_radical_span_sup_of_subset_radical_sup` / 引理 `Ideal.exists_subset_radical_span_sup_of_subset_radical_sup`

English:
lemma Ideal.exists_subset_radical_span_sup_of_subset_radical_sup
  statement: {R : Type*} [CommSemiring R]
  proof: by
  replace hs : forall z : s, exists (m : Nat) (a b : R) (ha : a in I) (hb : b in J), a + b = z ^ m := by
    rintro ⟨z, hzs⟩
    simp only [Ideal.radical, Submodule.mem_sup] at hs
    obtain ⟨m, y, hyq, b, hb, hy⟩ := hs hzs
    exact ⟨m, y, b, hyq, hb, hy⟩
  choose m a b ha hb heq using hs
  refi

中文:
引理 理想.存在_subset_radical_span_sup_of_subset_radical_sup
  结论: {R : 类型} [交换半环 R]
  证明: by
  replace hs : forall z : s, exists (m : Nat) (a b : R) (ha : a in I) (hb : b in J), a + b = z ^ m := by
    rintro ⟨z, hzs⟩
    simp only [Ideal.radical, Submodule.mem_sup] at hs
    obtain ⟨m, y, hyq, b, hb, hy⟩ := hs hzs
    exact ⟨m, y, b, hyq, hb, hy⟩
  choose m a b ha hb heq using hs
  refi

Depends on / 依赖: Ideal.add_mem, Ideal.radical, Set.range_subset_iff, Submodule, Submodule.mem_sup, add_mem, mem_sup, mem_sup_left, mem_sup_right, radical, range_subset_iff, replace, subset_span
-/
lemma Ideal.exists_subset_radical_span_sup_of_subset_radical_sup {R : Type*} [CommSemiring R]
    (s : Set R) (I J : Ideal R) (hs : s subseteq (I ⊔ J).radical) :
    exists (t : s -> R), Set.range t subseteq I ∧ s subseteq (span (Set.range t) ⊔ J).radical := by
  replace hs : forall z : s, exists (m : Nat) (a b : R) (ha : a in I) (hb : b in J), a + b = z ^ m := by
    rintro ⟨z, hzs⟩
    simp only [Ideal.radical, Submodule.mem_sup] at hs
    obtain ⟨m, y, hyq, b, hb, hy⟩ := hs hzs
    exact ⟨m, y, b, hyq, hb, hy⟩
  choose m a b ha hb heq using hs
  refine ⟨a, by rwa [Set.range_subset_iff], fun z hz => ⟨m ⟨z, hz⟩, heq ⟨z, hz⟩ ▸ ?_⟩⟩
  exact Ideal.add_mem _ (mem_sup_left (subset_span ⟨⟨z, hz⟩, rfl⟩)) (mem_sup_right <| hb _)
