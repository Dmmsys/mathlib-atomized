/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the clifford algebra

The main result is `CliffordAlgebra.gradedAlgebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

open scoped DirectSum

variable (Q)

/--
Definition of `evenOdd` / `evenOdd` 的定义

English:
definition evenOdd
  signature: (i : ZMod 2)
  body: ⨆ j : { n : Nat // ↑n = i }, LinearMap.range (ι Q) ^ (j : Nat)

中文:
定义 evenOdd
  签名: (i : ZMod 2)
  定义体: ⨆ j : { n : Nat // ↑n = i }, LinearMap.range (ι Q) ^ (j : Nat)

Depends on / 依赖: LinearMap, LinearMap.range
-/
def evenOdd (i : ZMod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : Nat // ↑n = i }, LinearMap.range (ι Q) ^ (j : Nat)

/--
theorem `one_le_evenOdd_zero` / 定理 `one_le_evenOdd_zero`

English:
theorem one_le_evenOdd_zero
  statement: 1 <= evenOdd Q 0
  proof: by
  refine le_trans ?_ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge

中文:
定理 one_le_evenOdd_zero
  结论: 1 <= evenOdd Q 0
  证明: by
  refine le_trans ?_ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge

Depends on / 依赖: Nat.cast_zero, cast_zero, le_iSup, le_trans, pow_zero
-/
theorem one_le_evenOdd_zero : 1 <= evenOdd Q 0 := by
  refine le_trans ?_ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge

/--
theorem `range_ι_le_evenOdd_one` / 定理 `range_ι_le_evenOdd_one`

English:
theorem range_ι_le_evenOdd_one
  statement: LinearMap.range (ι Q) <= evenOdd Q 1
  proof: by
  refine le_trans ?_ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge

中文:
定理 range_ι_le_evenOdd_one
  结论: 线性映射.range (ι Q) <= evenOdd Q 1
  证明: by
  refine le_trans ?_ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge

Depends on / 依赖: Nat.cast_one, cast_one, le_iSup, le_trans, pow_one
-/
theorem range_ι_le_evenOdd_one : LinearMap.range (ι Q) <= evenOdd Q 1 := by
  refine le_trans ?_ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge

/--
theorem `ι_mem_evenOdd_one` / 定理 `ι_mem_evenOdd_one`

English:
theorem ι_mem_evenOdd_one
  given: (m : M)
  statement: ι Q m in evenOdd Q 1
  proof: range_ι_le_evenOdd_one Q LinearMap.mem_range_self _ m

中文:
定理 ι_mem_evenOdd_one
  条件: (m : M)
  结论: ι Q m in evenOdd Q 1
  证明: range_ι_le_evenOdd_one Q LinearMap.mem_range_self _ m

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, mem_range_self
-/
theorem ι_mem_evenOdd_one (m : M) : ι Q m in evenOdd Q 1 :=
range_ι_le_evenOdd_one Q LinearMap.mem_range_self _ m

/--
theorem `ι_mul_ι_mem_evenOdd_zero` / 定理 `ι_mul_ι_mem_evenOdd_zero`

English:
theorem ι_mul_ι_mem_evenOdd_zero
  given: (m₁ m₂ : M)
  statement: ι Q m₁ * ι Q m₂ in evenOdd Q 0
  proof: Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk]; rw [pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))

中文:
定理 ι_mul_ι_mem_evenOdd_zero
  条件: (m₁ m₂ : M)
  结论: ι Q m₁ * ι Q m₂ in evenOdd Q 0
  证明: Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk]; rw [pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, Submodule, Submodule.mem_iSup_of_mem, Submodule.mul_mem_mul, Subtype, Subtype.coe_mk, coe_mk, mem_iSup_of_mem, mem_range_self, mul_mem_mul, pow_two
-/
theorem ι_mul_ι_mem_evenOdd_zero (m₁ m₂ : M) : ι Q m₁ * ι Q m₂ in evenOdd Q 0 :=
  Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk]; rw [pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))

/--
theorem `evenOdd_mul_le` / 定理 `evenOdd_mul_le`

English:
theorem evenOdd_mul_le
  given: (i j : ZMod 2)
  statement: evenOdd Q i * evenOdd Q j <= evenOdd Q (i + j)
  proof: by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  simp_rw [Set.iUnion_mul, Set.mul_iUnion, Set.iUnion_subset_iff, Set.mul_subset_iff]
  rintro ⟨xi, rfl⟩ ⟨yi, rfl⟩ x hx y hy
  refine Set.mem_iUnion.mpr ⟨⟨xi + yi, Nat.cast_add _ _⟩, ?_⟩
  simp only [

中文:
定理 evenOdd_mul_le
  条件: (i j : ZMod 2)
  结论: evenOdd Q i * evenOdd Q j <= evenOdd Q (i + j)
  证明: by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  simp_rw [Set.iUnion_mul, Set.mul_iUnion, Set.iUnion_subset_iff, Set.mul_subset_iff]
  rintro ⟨xi, rfl⟩ ⟨yi, rfl⟩ x hx y hy
  refine Set.mem_iUnion.mpr ⟨⟨xi + yi, Nat.cast_add _ _⟩, ?_⟩
  simp only [

Depends on / 依赖: Nat.cast_add, Set.iUnion_mul, Set.iUnion_subset_iff, Set.mem_iUnion.mpr, Set.mul_iUnion, Set.mul_subset_iff, Submodule, Submodule.iSup_eq_span, Submodule.mul_mem_mul, Submodule.span_mono, Submodule.span_mul_span, cast_add, evenOdd, iSup_eq_span, iUnion_mul, iUnion_subset_iff, mem_iUnion, mul_iUnion, mul_mem_mul, mul_subset_iff
-/
theorem evenOdd_mul_le (i j : ZMod 2) : evenOdd Q i * evenOdd Q j <= evenOdd Q (i + j) := by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  simp_rw [Set.iUnion_mul, Set.mul_iUnion, Set.iUnion_subset_iff, Set.mul_subset_iff]
  rintro ⟨xi, rfl⟩ ⟨yi, rfl⟩ x hx y hy
  refine Set.mem_iUnion.mpr ⟨⟨xi + yi, Nat.cast_add _ _⟩, ?_⟩
  simp only [pow_add]
  exact Submodule.mul_mem_mul hx hy

/--
Instance `evenOdd.gradedMonoid` / 实例 `evenOdd.gradedMonoid`

English:
instance evenOdd.gradedMonoid
  signature: : SetLike.GradedMonoid (evenOdd Q) where
  body: Submodule.one_le.mp (one_le_evenOdd_zero Q)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (evenOdd_mul_le Q _ _) _ hp _ hq

中文:
实例 evenOdd.gradedMonoid
  签名: : 集合状.分次幺半群 (evenOdd Q) where
  定义体: Submodule.one_le.mp (one_le_evenOdd_zero Q)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (evenOdd_mul_le Q _ _) _ hp _ hq

Depends on / 依赖: Submodule, Submodule.one_le.mp, one_le, one_le_evenOdd_zero
-/
instance evenOdd.gradedMonoid : SetLike.GradedMonoid (evenOdd Q) where
  one_mem := Submodule.one_le.mp (one_le_evenOdd_zero Q)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (evenOdd_mul_le Q _ _) _ hp _ hq

/--
Definition of `GradedAlgebra.ι` / `GradedAlgebra.ι` 的定义

English:
definition GradedAlgebra.ι
  signature: : M ->ₗ[R] ⨁ i : ZMod 2, evenOdd Q i
  body: DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)

中文:
定义 分次代数.ι
  签名: : M ->ₗ[R] ⨁ i : ZMod 2, evenOdd Q i
  定义体: DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)
-/
protected def GradedAlgebra.ι : M ->ₗ[R] ⨁ i : ZMod 2, evenOdd Q i :=
  DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)

/--
theorem `GradedAlgebra.ι_apply` / 定理 `GradedAlgebra.ι_apply`

English:
theorem GradedAlgebra.ι_apply
  given: (m : M)
  proof: rfl

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q]; rw [DirectSum.of_mul_of]; rw [DirectSum.algebraMap_apply]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scala

中文:
定理 分次代数.ι_apply
  条件: (m : M)
  证明: rfl

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q]; rw [DirectSum.of_mul_of]; rw [DirectSum.algebraMap_apply]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scala
-/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι Q m = DirectSum.of (fun i => ↥(evenOdd Q i)) 1 ⟨ι Q m, ι_mem_evenOdd_one Q m⟩ :=
  rfl

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q]; rw [DirectSum.of_mul_of]; rw [DirectSum.algebraMap_apply]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)

/--
theorem `GradedAlgebra.lift_ι_eq` / 定理 `GradedAlgebra.lift_ι_eq`

English:
theorem GradedAlgebra.lift_ι_eq
  given: (i' : ZMod 2) (x' : evenOdd Q i')
  proof: by
  obtain ⟨x', hx'⟩ := x'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨i, rfl⟩ := i
    dsimp only [Subtype.coe_mk] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
    

中文:
定理 分次代数.lift_ι_eq
  条件: (i' : ZMod 2) (x' : evenOdd Q i')
  证明: by
  obtain ⟨x', hx'⟩ := x'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨i, rfl⟩ := i
    dsimp only [Subtype.coe_mk] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
    

Depends on / 依赖: AlgHom, AlgHom.commutes, DirectSum, DirectSum.algebraMap_apply, DirectSum.lof_eq_of, Submodule, Submodule.iSup_induction, Submodule.pow_induction_on_left, Subtype, Subtype.coe_mk, algebraMap, algebraMap_apply, coe_mk, commutes, iSup_induction, lof_eq_of, map_add, map_mul, mem_mul, pow_induction_on_left
-/
theorem GradedAlgebra.lift_ι_eq (i' : ZMod 2) (x' : evenOdd Q i') :
    lift Q ⟨GradedAlgebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩ x' =
      DirectSum.of (fun i => evenOdd Q i) i' x' := by
  obtain ⟨x', hx'⟩ := x'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨i, rfl⟩ := i
    dsimp only [Subtype.coe_mk] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes]; rw [DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add]; rw [ihx]; rw [ihy]; rw [← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul]; rw [ih]; rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply Q]; rw [DirectSum.of_mul_of]
      refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ ?_) <;>
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
      · rw [Nat.succ_eq_add_one, add_comm, Nat.cast_add, Nat.cast_one]
      rfl
  | zero =>
    rw [map_zero]
    apply Eq.symm
    apply DFinsupp.single_eq_zero.mpr; rfl
  | add x y hx hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]; rw [← map_add]; rfl

/--
Instance `gradedAlgebra` / 实例 `gradedAlgebra`

English:
instance gradedAlgebra
  signature: : GradedAlgebra (evenOdd Q)
  body: GradedAlgebra.ofAlgHom (evenOdd Q)
    -- while not necessary, the `by apply` makes this elaborate faster
    (lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩)
    -- the proof from here onward is mostly similar to the `TensorAlgebra` case, with some extra
    -- handling f

中文:
实例 gradedAlgebra
  签名: : 分次代数 (evenOdd Q)
  定义体: GradedAlgebra.ofAlgHom (evenOdd Q)
    -- while not necessary, the `by apply` makes this elaborate faster
    (lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩)
    -- the proof from here onward is mostly similar to the `TensorAlgebra` case, with some extra
    -- handling f

Depends on / 依赖: GradedAlgebra, GradedAlgebra.ofAlgHom, evenOdd, ofAlgHom
-/
instance gradedAlgebra : GradedAlgebra (evenOdd Q) :=
  GradedAlgebra.ofAlgHom (evenOdd Q)
    -- while not necessary, the `by apply` makes this elaborate faster
    (lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩)
    -- the proof from here onward is mostly similar to the `TensorAlgebra` case, with some extra
    -- handling for the `iSup` in `evenOdd`.
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply Q]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.coe_mk])
    (by apply GradedAlgebra.lift_ι_eq Q)

/--
theorem `iSup_ι_range_eq_top` / 定理 `iSup_ι_range_eq_top`

English:
theorem iSup_ι_range_eq_top
  statement: ⨆ i : Nat, LinearMap.range (ι Q) ^ i = ⊤
  proof: by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top]; rw [eq_comm]
  calc
    -- Porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : Nat // ↑n = i }), LinearMap.range (ι Q) ^ (j : Nat) =

中文:
定理 iSup_ι_range_eq_top
  结论: ⨆ i : 自然数, 线性映射.range (ι Q) ^ i = ⊤
  证明: by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top]; rw [eq_comm]
  calc
    -- Porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : Nat // ↑n = i }), LinearMap.range (ι Q) ^ (j : Nat) =

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.isInternal, eq_comm, evenOdd, isInternal, submodule_iSup_eq_top
-/
theorem iSup_ι_range_eq_top : ⨆ i : Nat, LinearMap.range (ι Q) ^ i = ⊤ := by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top]; rw [eq_comm]
  calc
    -- Porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : Nat // ↑n = i }), LinearMap.range (ι Q) ^ (j : Nat) =
        ⨆ i : Σ i : ZMod 2, { n : Nat // ↑n = i }, LinearMap.range (ι Q) ^ (i.2 : Nat) := by
      rw [iSup_sigma]
    _ = ⨆ i : Nat, LinearMap.range (ι Q) ^ i :=
      Function.Surjective.iSup_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl

/--
theorem `evenOdd_isCompl` / 定理 `evenOdd_isCompl`

English:
theorem evenOdd_isCompl
  statement: IsCompl (evenOdd Q 0) (evenOdd Q 1)
  proof: (DirectSum.Decomposition.isInternal (evenOdd Q)).isCompl zero_ne_one by
    have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    simpa using congr_arg ((↑) : Finset (ZMod 2) -> Set (ZMod 2)) this

中文:
定理 evenOdd_isCompl
  结论: 是补集 (evenOdd Q 0) (evenOdd Q 1)
  证明: (DirectSum.Decomposition.isInternal (evenOdd Q)).isCompl zero_ne_one by
    have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    simpa using congr_arg ((↑) : Finset (ZMod 2) -> Set (ZMod 2)) this

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.isInternal, Finset, Finset.univ, congr_arg, evenOdd, isCompl, isInternal, zero_ne_one
-/
theorem evenOdd_isCompl : IsCompl (evenOdd Q 0) (evenOdd Q 1) :=
(DirectSum.Decomposition.isInternal (evenOdd Q)).isCompl zero_ne_one by
    have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    simpa using congr_arg ((↑) : Finset (ZMod 2) -> Set (ZMod 2)) this

/-- To show a property is true on the even or odd part, it suffices to show it is true on the
scalars or vectors (respectively), closed under addition, and under left-multiplication by a pair
of vectors. -/
@[elab_as_elim]
/--
theorem `evenOdd_induction` / 定理 `evenOdd_induction`

English:
theorem evenOdd_induction
  statement: (n : ZMod 2) {motive : forall x, x in evenOdd Q n -> Prop}
  proof: by
  apply Submodule.iSup_induction' (motive := motive) _ _ (range_ι_pow 0 (Submodule.zero_mem _)) add
  refine Subtype.rec ?_
  simp_rw [ZMod.natCast_eq_iff, add_comm n.val]
  rintro n' ⟨k, rfl⟩ xv
  simp_rw [pow_add, pow_mul]
  intro hxv
  induction hxv using Submodule.mul_induction_on' with
  | m

中文:
定理 evenOdd_induction
  结论: (n : ZMod 2) {motive : 对任意 x, x in evenOdd Q n -> 命题}
  证明: by
  apply Submodule.iSup_induction' (motive := motive) _ _ (range_ι_pow 0 (Submodule.zero_mem _)) add
  refine Subtype.rec ?_
  simp_rw [ZMod.natCast_eq_iff, add_comm n.val]
  rintro n' ⟨k, rfl⟩ xv
  simp_rw [pow_add, pow_mul]
  intro hxv
  induction hxv using Submodule.mul_induction_on' with
  | m

Depends on / 依赖: Algebra, Algebra.smul_def, Submodule, Submodule.iSup_induction, Submodule.mul_induction_on, Submodule.pow_induction_on_left, Submodule.smul_mem, Submodule.zero_mem, Subtype, Subtype.rec, ZMod.natCast_eq_iff, add_comm, algebraMap, iSup_induction, mem_mul_mem, motive, mul_induction_on, n.val, natCast_eq_iff, pow_add
-/
theorem evenOdd_induction (n : ZMod 2) {motive : forall x, x in evenOdd Q n -> Prop}
    (range_ι_pow : forall (v) (h : v in LinearMap.range (ι Q) ^ n.val),
        motive v (Submodule.mem_iSup_of_mem ⟨n.val, n.natCast_zmod_val⟩ h))
    (add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      forall m₁ m₂ x hx,
        motive x hx ->
          motive (ι Q m₁ * ι Q m₂ * x)
            (zero_add n ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x in evenOdd Q n) : motive x hx := by
  apply Submodule.iSup_induction' (motive := motive) _ _ (range_ι_pow 0 (Submodule.zero_mem _)) add
  refine Subtype.rec ?_
  simp_rw [ZMod.natCast_eq_iff, add_comm n.val]
  rintro n' ⟨k, rfl⟩ xv
  simp_rw [pow_add, pow_mul]
  intro hxv
  induction hxv using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
    induction ha using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      simp_rw [← Algebra.smul_def]
      exact range_ι_pow _ (Submodule.smul_mem _ _ hb)
    | add x y n hx hy ihx ihy =>
      simp_rw [add_mul]
      apply add _ _ _ _ ihx ihy
    | mem_mul x hx n'' y hy ihy =>
      revert hx
      simp_rw [pow_two]
      intro hx2
      induction hx2 using Submodule.mul_induction_on' with
      | mem_mul_mem m hm n hn =>
        simp_rw [LinearMap.mem_range] at hm hn
        obtain ⟨m₁, rfl⟩ := hm; obtain ⟨m₂, rfl⟩ := hn
        simp_rw [mul_assoc _ y b]
        exact ι_mul_ι_mul _ _ _ _ ihy
      | add x hx y hy ihx ihy =>
        simp_rw [add_mul]
        apply add _ _ _ _ ihx ihy
  | add x y hx hy ihx ihy =>
    apply add _ _ _ _ ihx ihy

/-- To show a property is true on the even parts, it suffices to show it is true on the
scalars, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
/--
theorem `even_induction` / 定理 `even_induction`

English:
theorem even_induction
  statement: {motive : forall x, x in evenOdd Q 0 -> Prop}
  proof: by
  refine evenOdd_induction _ _ (motive := motive) (fun rx h => ?_) add ι_mul_ι_mul x hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h
  exact algebraMap r

中文:
定理 even_induction
  结论: {motive : 对任意 x, x in evenOdd Q 0 -> 命题}
  证明: by
  refine evenOdd_induction _ _ (motive := motive) (fun rx h => ?_) add ι_mul_ι_mul x hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h
  exact algebraMap r

Depends on / 依赖: Submodule, Submodule.mem_one.mp, algebraMap, evenOdd_induction, mem_one, motive
-/
theorem even_induction {motive : forall x, x in evenOdd Q 0 -> Prop}
    (algebraMap : forall r : R, motive (algebraMap _ _ r) (SetLike.algebraMap_mem_graded _ _))
    (add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      forall m₁ m₂ x hx,
        motive x hx ->
          motive (ι Q m₁ * ι Q m₂ * x)
            (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x in evenOdd Q 0) : motive x hx := by
  refine evenOdd_induction _ _ (motive := motive) (fun rx h => ?_) add ι_mul_ι_mul x hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h
  exact algebraMap r

/-- To show a property is true on the odd parts, it suffices to show it is true on the
vectors, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
/--
theorem `odd_induction` / 定理 `odd_induction`

English:
theorem odd_induction
  statement: {P : forall x, x in evenOdd Q 1 -> Prop}
  proof: by
  refine evenOdd_induction _ _ (motive := P) (fun ιv => ?_) add ι_mul_ι_mul x hx
  simp_rw [ZMod.val_one, pow_one]
  rintro ⟨v, rfl⟩
  exact ι v

中文:
定理 odd_induction
  结论: {P : 对任意 x, x in evenOdd Q 1 -> 命题}
  证明: by
  refine evenOdd_induction _ _ (motive := P) (fun ιv => ?_) add ι_mul_ι_mul x hx
  simp_rw [ZMod.val_one, pow_one]
  rintro ⟨v, rfl⟩
  exact ι v

Depends on / 依赖: ZMod.val_one, evenOdd_induction, motive, pow_one, simp_rw, val_one
-/
theorem odd_induction {P : forall x, x in evenOdd Q 1 -> Prop}
    (ι : forall v, P (ι Q v) (ι_mem_evenOdd_one _ _))
    (add : forall x y hx hy, P x hx -> P y hy -> P (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      forall m₁ m₂ x hx,
        P x hx ->
          P (CliffordAlgebra.ι Q m₁ * CliffordAlgebra.ι Q m₂ * x)
            (zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x in evenOdd Q 1) : P x hx := by
  refine evenOdd_induction _ _ (motive := P) (fun ιv => ?_) add ι_mul_ι_mul x hx
  simp_rw [ZMod.val_one, pow_one]
  rintro ⟨v, rfl⟩
  exact ι v

end CliffordAlgebra
