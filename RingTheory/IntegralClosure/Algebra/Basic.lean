/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integral closure of a subring.

Let `A` be an `R`-algebra. We prove that integral elements form a sub-`R`-algebra of `A`.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `integralClosure R A` : the integral closure of `R` in an `R`-algebra `A`.
-/

@[expose] public section


open Polynomial Submodule

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R ->+* S)

/--
theorem `Subalgebra.isIntegral_iff` / 定理 `Subalgebra.isIntegral_iff`

English:
theorem Subalgebra.isIntegral_iff
  given: (S : Subalgebra R B)
  proof: Algebra.isIntegral_def.trans .trans
    (forall_congr' fun _ => (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

中文:
定理 子代数.is整数egral_iff
  条件: (S : 子代数 R B)
  证明: Algebra.isIntegral_def.trans .trans
    (forall_congr' fun _ => (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

Depends on / 依赖: Algebra, Algebra.isIntegral_def.trans, S.val, Subtype, Subtype.forall, Subtype.val_injective, forall_congr, isIntegral_algHom_iff, isIntegral_def, val_injective
-/
theorem Subalgebra.isIntegral_iff (S : Subalgebra R B) :
    Algebra.IsIntegral R S ↔ forall x in S, IsIntegral R x :=
Algebra.isIntegral_def.trans .trans
    (forall_congr' fun _ => (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/--
theorem `Algebra.IsIntegral.of_injective` / 定理 `Algebra.IsIntegral.of_injective`

English:
theorem Algebra.IsIntegral.of_injective
  statement: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: ⟨fun _ => (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

中文:
定理 代数.是整.of_injective
  结论: (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: ⟨fun _ => (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

Depends on / 依赖: isIntegral, isIntegral_algHom_iff
-/
theorem Algebra.IsIntegral.of_injective (f : A ->ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsIntegral R B] : Algebra.IsIntegral R A :=
  ⟨fun _ => (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

/--
theorem `Algebra.IsIntegral.of_surjective` / 定理 `Algebra.IsIntegral.of_surjective`

English:
theorem Algebra.IsIntegral.of_surjective
  statement: [Algebra.IsIntegral R A]
  proof: isIntegral_def.mpr fun b => let ⟨a, ha⟩ := hf b; ha ▸ (isIntegral_def.mp ‹_› a).map f

中文:
定理 代数.是整.of_surjective
  结论: [代数.是整 R A]
  证明: isIntegral_def.mpr fun b => let ⟨a, ha⟩ := hf b; ha ▸ (isIntegral_def.mp ‹_› a).map f

Depends on / 依赖: isIntegral_def, isIntegral_def.mp, isIntegral_def.mpr
-/
theorem Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A]
    (f : A ->ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  isIntegral_def.mpr fun b => let ⟨a, ha⟩ := hf b; ha ▸ (isIntegral_def.mp ‹_› a).map f

/--
theorem `AlgEquiv.isIntegral_iff` / 定理 `AlgEquiv.isIntegral_iff`

English:
theorem AlgEquiv.isIntegral_iff
  given: (e : A ≃ₐ[R] B)
  statement: Algebra.IsIntegral R A ↔ Algebra.IsIntegral R B
  proof: ⟨fun h => h.of_injective e.symm e.symm.injective, fun h => h.of_injective e e.injective⟩

中文:
定理 代数等价.is整数egral_iff
  条件: (e : A ≃ₐ[R] B)
  结论: 代数.是整 R A ↔ 代数.是整 R B
  证明: ⟨fun h => h.of_injective e.symm e.symm.injective, fun h => h.of_injective e e.injective⟩

Depends on / 依赖: e.injective, e.symm, e.symm.injective, h.of_injective, injective, of_injective
-/
theorem AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algebra.IsIntegral R A ↔ Algebra.IsIntegral R B :=
  ⟨fun h => h.of_injective e.symm e.symm.injective, fun h => h.of_injective e e.injective⟩

end

/--
Instance `Module.End.isIntegral` / 实例 `Module.End.isIntegral`

English:
instance Module.End.isIntegral
  signature: {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  body: ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩

中文:
实例 模.End.is整数egral
  签名: {M : 类型} [加法交换群 M] [模 R M] [模.有限 R M]
  定义体: ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩

Depends on / 依赖: LinearMap, LinearMap.exists_monic_and_aeval_eq_zero, exists_monic_and_aeval_eq_zero
-/
instance Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Algebra.IsIntegral R (Module.End R M) :=
  ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩

variable (R) in
@[nontriviality]
/--
theorem `IsIntegral.of_finite` / 定理 `IsIntegral.of_finite`

English:
theorem IsIntegral.of_finite
  given: [Module.Finite R B] (x : B)
  statement: IsIntegral R x
  proof: (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)

中文:
定理 是整.of_finite
  条件: [模.有限 R B] (x : B)
  结论: 是整 R x
  证明: (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Algebra.lmul, Algebra.lmul_injective, IsIntegral, isIntegral, isIntegral_algHom_iff, lmul_injective
-/
theorem IsIntegral.of_finite [Module.Finite R B] (x : B) : IsIntegral R x :=
  (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)

/--
theorem `isIntegral_of_noetherian` / 定理 `isIntegral_of_noetherian`

English:
theorem isIntegral_of_noetherian
  given: (_ : IsNoetherian R B) (x : B)
  statement: IsIntegral R x
  proof: .of_finite R x

中文:
定理 is整数egral_of_noetherian
  条件: (_ : 是Noether R B) (x : B)
  结论: 是整 R x
  证明: .of_finite R x

Depends on / 依赖: of_finite
-/
theorem isIntegral_of_noetherian (_ : IsNoetherian R B) (x : B) : IsIntegral R x :=
  .of_finite R x

variable (R B) in
/--
Instance `Algebra.IsIntegral.of_finite` / 实例 `Algebra.IsIntegral.of_finite`

English:
instance Algebra.IsIntegral.of_finite
  signature: [Module.Finite R B]
  body: ⟨.of_finite R⟩

中文:
实例 代数.是整.of_finite
  签名: [模.有限 R B]
  定义体: ⟨.of_finite R⟩

Depends on / 依赖: of_finite
-/
instance Algebra.IsIntegral.of_finite [Module.Finite R B] : Algebra.IsIntegral R B :=
  ⟨.of_finite R⟩

/--
lemma `Algebra.isIntegral_of_surjective` / 引理 `Algebra.isIntegral_of_surjective`

English:
lemma Algebra.isIntegral_of_surjective
  given: (H : Function.Surjective (algebraMap R B))
  proof: .of_surjective (Algebra.ofId R B) H

中文:
引理 代数.is整数egral_of_surjective
  条件: (H : 函数.满射 (algebraMap R B))
  证明: .of_surjective (Algebra.ofId R B) H

Depends on / 依赖: Algebra, Algebra.ofId, of_surjective
-/
lemma Algebra.isIntegral_of_surjective (H : Function.Surjective (algebraMap R B)) :
    Algebra.IsIntegral R B :=
  .of_surjective (Algebra.ofId R B) H

/--
theorem `IsIntegral.of_mem_of_fg` / 定理 `IsIntegral.of_mem_of_fg`

English:
theorem IsIntegral.of_mem_of_fg
  statement: (S : Subalgebra R B)
  proof: have : Module.Finite R S := .of_fg HS
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))

中文:
定理 是整.of_mem_of_fg
  结论: (S : 子代数 R B)
  证明: have : Module.Finite R S := .of_fg HS
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))

Depends on / 依赖: Finite, Module, Module.Finite, S.val, Subtype, Subtype.val_injective, isIntegral_algHom_iff, of_fg, of_finite, val_injective
-/
theorem IsIntegral.of_mem_of_fg (S : Subalgebra R B)
    (HS : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x :=
  have : Module.Finite R S := .of_fg HS
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))

/--
theorem `isIntegral_of_submodule_noetherian` / 定理 `isIntegral_of_submodule_noetherian`

English:
theorem isIntegral_of_submodule_noetherian
  statement: (S : Subalgebra R B)
  proof: .of_mem_of_fg _ ((Submodule.fg_top _).mp <| H.noetherian _) _ hx

中文:
定理 is整数egral_of_submodule_noetherian
  结论: (S : 子代数 R B)
  证明: .of_mem_of_fg _ ((Submodule.fg_top _).mp <| H.noetherian _) _ hx

Depends on / 依赖: H.noetherian, Submodule, Submodule.fg_top, fg_top, noetherian, of_mem_of_fg
-/
theorem isIntegral_of_submodule_noetherian (S : Subalgebra R B)
    (H : IsNoetherian R (Subalgebra.toSubmodule S)) (x : B) (hx : x in S) : IsIntegral R x :=
  .of_mem_of_fg _ ((Submodule.fg_top _).mp <| H.noetherian _) _ hx

/--
theorem `isIntegral_of_smul_mem_submodule` / 定理 `isIntegral_of_smul_mem_submodule`

English:
theorem isIntegral_of_smul_mem_submodule
  statement: [IsDomain A] {M : Type*} [AddCommGroup M] [Module R M]
  proof: by
  let A' : Subalgebra R A :=
    { carrier := { x | forall n in N, x • n in N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' ->ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribSMul.toLinearMap R M x).restrict x.prop
        map_add' := by intro x y; ext; exact add_smul _ _ _
        map_smul' := by intro r s; ext; apply smul_assoc }
      (by ext; apply one_smul)
      (by intro x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : exists a in N, a != (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    change Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((smul_eq_zero_iff_left ha₂).1 this)
  change IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective]; rw [← isIntegral_algHom_iff f this]
  have : Module.Finite R N := by rwa [Module.Finite.iff_fg]
  apply Algebra.IsIntegral.isIntegral

中文:
定理 is整数egral_of_smul_mem_submodule
  结论: [是整环 A] {M : 类型} [加法交换群 M] [模 R M]
  证明: by
  let A' : Subalgebra R A :=
    { carrier := { x | forall n in N, x • n in N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' ->ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribSMul.toLinearMap R M x).restrict x.prop
        map_add' := by intro x y; ext; exact add_smul _ _ _
        map_smul' := by intro r s; ext; apply smul_assoc }
      (by ext; apply one_smul)
      (by intro x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : exists a in N, a != (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    change Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((smul_eq_zero_iff_left ha₂).1 this)
  change IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective]; rw [← isIntegral_algHom_iff f this]
  have : Module.Finite R N := by rwa [Module.Finite.iff_fg]
  apply Algebra.IsIntegral.isIntegral

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, Module, Module.End, N.add_mem, N.smul_mem, N.zero_mem, Subalgebra, add_mem, add_smul, algebraMap_mem, algebraMap_smul, carrier, mul_mem, ofLinearMap, one_mem, one_smul, smul_mem, smul_smul, zero_mem
-/
theorem isIntegral_of_smul_mem_submodule [IsDomain A] {M : Type*} [AddCommGroup M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module.IsTorsionFree A M] (N : Submodule R M) (hN : N != ⊥)
    (hN' : N.FG) (x : A) (hx : forall n in N, x • n in N) : IsIntegral R x := by
  let A' : Subalgebra R A :=
    { carrier := { x | forall n in N, x • n in N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' ->ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribSMul.toLinearMap R M x).restrict x.prop
        map_add' := by intro x y; ext; exact add_smul _ _ _
        map_smul' := by intro r s; ext; apply smul_assoc }
      (by ext; apply one_smul)
      (by intro x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : exists a in N, a != (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    change Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((smul_eq_zero_iff_left ha₂).1 this)
  change IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective]; rw [← isIntegral_algHom_iff f this]
  have : Module.Finite R N := by rwa [Module.Finite.iff_fg]
  apply Algebra.IsIntegral.isIntegral

variable {f}

@[stacks 00GK]
/--
theorem `RingHom.Finite.to_isIntegral` / 定理 `RingHom.Finite.to_isIntegral`

English:
theorem RingHom.Finite.to_isIntegral
  given: (h : f.Finite)
  statement: f.IsIntegral
  proof: letI := f.toAlgebra
  fun _ => IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral

中文:
定理 环态射.有限.to_is整数egral
  条件: (h : f.有限)
  结论: f.是整
  证明: letI := f.toAlgebra
  fun _ => IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral

Depends on / 依赖: IsIntegral, IsIntegral.of_mem_of_fg, f.toAlgebra, of_mem_of_fg, toAlgebra
-/
theorem RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral :=
  letI := f.toAlgebra
  fun _ => IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral

variable (f)

/--
theorem `RingHom.IsIntegralElem.of_mem_closure` / 定理 `RingHom.IsIntegralElem.of_mem_closure`

English:
theorem RingHom.IsIntegralElem.of_mem_closure
  statement: {x y z : S} (hx : f.IsIntegralElem x)
  proof: by
  let : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule]; rw [Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)

nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z in Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz

中文:
定理 环态射.Is整数egralElem.of_mem_closure
  结论: {x y z : S} (hx : f.Is整数egralElem x)
  证明: by
  let : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule]; rw [Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)

nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z in Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_union_coe_submodule, Algebra.mem_adjoin_iff, IsIntegral, IsIntegral.fg_adjoin_singleton, IsIntegral.of_mem_of_fg, Set.singleton_union, Set.subset_union_right, Subring, Subring.closure_mono, adjoin, adjoin_union_coe_submodule, closure_mono, f.toAlgebra, fg_adjoin_singleton, mem_adjoin_iff, of_mem_of_fg, singleton_union, subset_union_right
-/
theorem RingHom.IsIntegralElem.of_mem_closure {x y z : S} (hx : f.IsIntegralElem x)
    (hy : f.IsIntegralElem y) (hz : z in Subring.closure ({x, y} : Set S)) : f.IsIntegralElem z := by
  let : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule]; rw [Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)

nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z in Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz

variable (f : R ->+* B)

/--
theorem `RingHom.IsIntegralElem.add` / 定理 `RingHom.IsIntegralElem.add`

English:
theorem RingHom.IsIntegralElem.add
  statement: (f : R ->+* S) {x y : S}
  proof: hx.of_mem_closure f hy
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy

中文:
定理 环态射.Is整数egralElem.add
  结论: (f : R ->+* S) {x y : S}
  证明: hx.of_mem_closure f hy
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy

Depends on / 依赖: Or.inl, Or.inr, Subring, Subring.add_mem, Subring.subset_closure, add_mem, hx.of_mem_closure, of_mem_closure, subset_closure
-/
theorem RingHom.IsIntegralElem.add (f : R ->+* S) {x y : S}
    (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x + y) :=
hx.of_mem_closure f hy
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy

variable (f : R ->+* S)

-- can be generalized to noncommutative S.
/--
theorem `RingHom.IsIntegralElem.neg` / 定理 `RingHom.IsIntegralElem.neg`

English:
theorem RingHom.IsIntegralElem.neg
  given: {x : S} (hx : f.IsIntegralElem x)
  statement: f.IsIntegralElem (-x)
  proof: hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))

中文:
定理 环态射.Is整数egralElem.neg
  条件: {x : S} (hx : f.Is整数egralElem x)
  结论: f.Is整数egralElem (-x)
  证明: hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))

Depends on / 依赖: Or.inl, Subring, Subring.neg_mem, Subring.subset_closure, hx.of_mem_closure, neg_mem, of_mem_closure, subset_closure
-/
theorem RingHom.IsIntegralElem.neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegralElem (-x) :=
  hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))

/--
theorem `RingHom.IsIntegralElem.of_neg` / 定理 `RingHom.IsIntegralElem.of_neg`

English:
theorem RingHom.IsIntegralElem.of_neg
  given: {x : S} (h : f.IsIntegralElem (-x))
  statement: f.IsIntegralElem x
  proof: neg_neg x ▸ h.neg

@[simp]

中文:
定理 环态射.Is整数egralElem.of_neg
  条件: {x : S} (h : f.Is整数egralElem (-x))
  结论: f.Is整数egralElem x
  证明: neg_neg x ▸ h.neg

@[simp]

Depends on / 依赖: h.neg, neg_neg
-/
theorem RingHom.IsIntegralElem.of_neg {x : S} (h : f.IsIntegralElem (-x)) : f.IsIntegralElem x :=
  neg_neg x ▸ h.neg

@[simp]
/--
theorem `RingHom.IsIntegralElem.neg_iff` / 定理 `RingHom.IsIntegralElem.neg_iff`

English:
theorem RingHom.IsIntegralElem.neg_iff
  given: {x : S}
  statement: f.IsIntegralElem (-x) ↔ f.IsIntegralElem x
  proof: ⟨fun h => h.of_neg, fun h => h.neg⟩

中文:
定理 环态射.Is整数egralElem.neg_iff
  条件: {x : S}
  结论: f.Is整数egralElem (-x) ↔ f.Is整数egralElem x
  证明: ⟨fun h => h.of_neg, fun h => h.neg⟩

Depends on / 依赖: h.neg, h.of_neg, of_neg
-/
theorem RingHom.IsIntegralElem.neg_iff {x : S} : f.IsIntegralElem (-x) ↔ f.IsIntegralElem x :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩

/--
theorem `IsIntegral.neg` / 定理 `IsIntegral.neg`

English:
theorem IsIntegral.neg
  given: {x : B} (hx : IsIntegral R x)
  statement: IsIntegral R (-x)
  proof: .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)

中文:
定理 是整.neg
  条件: {x : B} (hx : 是整 R x)
  结论: 是整 R (-x)
  证明: .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Subalgebra, Subalgebra.neg_mem, fg_adjoin_singleton, hx.fg_adjoin_singleton, neg_mem, of_mem_of_fg, subset_adjoin
-/
theorem IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)

/--
theorem `IsIntegral.of_neg` / 定理 `IsIntegral.of_neg`

English:
theorem IsIntegral.of_neg
  given: {x : B} (hx : IsIntegral R (-x))
  statement: IsIntegral R x
  proof: neg_neg x ▸ hx.neg

@[simp]

中文:
定理 是整.of_neg
  条件: {x : B} (hx : 是整 R (-x))
  结论: 是整 R x
  证明: neg_neg x ▸ hx.neg

@[simp]

Depends on / 依赖: hx.neg, neg_neg
-/
theorem IsIntegral.of_neg {x : B} (hx : IsIntegral R (-x)) : IsIntegral R x :=
  neg_neg x ▸ hx.neg

@[simp]
/--
theorem `IsIntegral.neg_iff` / 定理 `IsIntegral.neg_iff`

English:
theorem IsIntegral.neg_iff
  given: {x : B}
  statement: IsIntegral R (-x) ↔ IsIntegral R x
  proof: ⟨IsIntegral.of_neg, IsIntegral.neg⟩

中文:
定理 是整.neg_iff
  条件: {x : B}
  结论: 是整 R (-x) ↔ 是整 R x
  证明: ⟨IsIntegral.of_neg, IsIntegral.neg⟩

Depends on / 依赖: IsIntegral, IsIntegral.neg, IsIntegral.of_neg, of_neg
-/
theorem IsIntegral.neg_iff {x : B} : IsIntegral R (-x) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_neg, IsIntegral.neg⟩

/--
theorem `RingHom.IsIntegralElem.sub` / 定理 `RingHom.IsIntegralElem.sub`

English:
theorem RingHom.IsIntegralElem.sub
  given: {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y)
  proof: by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)

nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy

中文:
定理 环态射.Is整数egralElem.sub
  条件: {x y : S} (hx : f.Is整数egralElem x) (hy : f.Is整数egralElem y)
  证明: by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)

nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy

Depends on / 依赖: hx.add, hy.neg, sub_eq_add_neg
-/
theorem RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)

nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy

/--
theorem `RingHom.IsIntegralElem.mul` / 定理 `RingHom.IsIntegralElem.mul`

English:
theorem RingHom.IsIntegralElem.mul
  given: {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y)
  proof: hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy

中文:
定理 环态射.Is整数egralElem.mul
  条件: {x y : S} (hx : f.Is整数egralElem x) (hy : f.Is整数egralElem y)
  证明: hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy

Depends on / 依赖: Or.inl, Or.inr, Subring, Subring.mul_mem, Subring.subset_closure, hx.of_mem_closure, mul_mem, of_mem_closure, subset_closure
-/
theorem RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x * y) :=
  hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy

/--
theorem `IsIntegral.smul` / 定理 `IsIntegral.smul`

English:
theorem IsIntegral.smul
  statement: {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra R S]
  proof: .of_mem_of_fg _ hx.fg_adjoin_singleton _ by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl

中文:
定理 是整.smul
  结论: {R} [交换半环 R] [代数 R B] [代数 S B] [代数 R S]
  证明: .of_mem_of_fg _ hx.fg_adjoin_singleton _ by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Subalgebra, Subalgebra.smul_mem, algebraMap_smul, fg_adjoin_singleton, hx.fg_adjoin_singleton, of_mem_of_fg, smul_mem, subset_adjoin
-/
theorem IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra R S]
    [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S x) : IsIntegral S (r • x) :=
.of_mem_of_fg _ hx.fg_adjoin_singleton _ by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl

/--
theorem `isIntegral_intCast` / 定理 `isIntegral_intCast`

English:
theorem isIntegral_intCast
  given: (n : Int)
  statement: IsIntegral R (n : B)
  proof: by
  rw [← map_intCast (_ : R ->+* B) n]
  exact isIntegral_algebraMap

中文:
定理 is整数egral_intCast
  条件: (n : 整数)
  结论: 是整 R (n : B)
  证明: by
  rw [← map_intCast (_ : R ->+* B) n]
  exact isIntegral_algebraMap

Depends on / 依赖: isIntegral_algebraMap, map_intCast
-/
theorem isIntegral_intCast (n : Int) : IsIntegral R (n : B) := by
  rw [← map_intCast (_ : R ->+* B) n]
  exact isIntegral_algebraMap

/--
theorem `isIntegral_natCast` / 定理 `isIntegral_natCast`

English:
theorem isIntegral_natCast
  given: (a : Nat)
  statement: IsIntegral R (a : B)
  proof: by
  rw [← Int.cast_natCast]
  exact isIntegral_intCast a

中文:
定理 is整数egral_natCast
  条件: (a : 自然数)
  结论: 是整 R (a : B)
  证明: by
  rw [← Int.cast_natCast]
  exact isIntegral_intCast a

Depends on / 依赖: Int.cast_natCast, cast_natCast, isIntegral_intCast
-/
theorem isIntegral_natCast (a : Nat) : IsIntegral R (a : B) := by
  rw [← Int.cast_natCast]
  exact isIntegral_intCast a

variable (R A)

/--
Definition of `integralClosure` / `integralClosure` 的定义

English:
definition integralClosure
  signature: : Subalgebra R A where
  body: { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap

中文:
定义 integralClosure
  签名: : 子代数 R A where
  定义体: { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap

Depends on / 依赖: IsIntegral
-/
def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap

/--
theorem `mem_integralClosure_iff` / 定理 `mem_integralClosure_iff`

English:
theorem mem_integralClosure_iff
  given: {a : A}
  statement: a in integralClosure R A ↔ IsIntegral R a
  proof: Iff.rfl

中文:
定理 mem_integralClosure_iff
  条件: {a : A}
  结论: a in integralClosure R A ↔ 是整 R a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_integralClosure_iff {a : A} : a in integralClosure R A ↔ IsIntegral R a :=
  Iff.rfl

variable {R} {A B : Type*} [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/--
Instance `Algebra.IsIntegral.prod` / 实例 `Algebra.IsIntegral.prod`

English:
instance Algebra.IsIntegral.prod
  signature: [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
  body: Algebra.isIntegral_def.mpr fun x =>
    (Algebra.isIntegral_def.mp ‹_› x.1).pair (Algebra.isIntegral_def.mp ‹_› x.2)

中文:
实例 代数.是整.乘积
  签名: [代数.是整 R A] [代数.是整 R B]
  定义体: Algebra.isIntegral_def.mpr fun x =>
    (Algebra.isIntegral_def.mp ‹_› x.1).pair (Algebra.isIntegral_def.mp ‹_› x.2)

Depends on / 依赖: Algebra, Algebra.isIntegral_def.mp, Algebra.isIntegral_def.mpr, isIntegral_def
-/
instance Algebra.IsIntegral.prod [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R (A × B) :=
  Algebra.isIntegral_def.mpr fun x =>
    (Algebra.isIntegral_def.mp ‹_› x.1).pair (Algebra.isIntegral_def.mp ‹_› x.2)

end

section TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A]

open TensorProduct

/--
theorem `IsIntegral.tmul` / 定理 `IsIntegral.tmul`

English:
theorem IsIntegral.tmul
  statement: [Ring B] [Algebra R A] [Algebra R B]
  proof: by
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [← smul_tmul']
  exact smul _ (h.map_of_comp_eq (algebraMap R A)
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

中文:
定理 是整.tmul
  结论: [环 B] [代数 R A] [代数 R B]
  证明: by
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [← smul_tmul']
  exact smul _ (h.map_of_comp_eq (algebraMap R A)
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, Algebra.TensorProduct.includeRight, TensorProduct, algebraMap, h.map_of_comp_eq, includeLeftRingHom_comp_algebraMap, includeRight, map_of_comp_eq, mul_one, smul_eq_mul, smul_tmul, toRingHom
-/
theorem IsIntegral.tmul [Ring B] [Algebra R A] [Algebra R B]
    (x : A) {y : B} (h : IsIntegral R y) : IsIntegral A (x otimesₜ[R] y) := by
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [← smul_tmul']
  exact smul _ (h.map_of_comp_eq (algebraMap R A)
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

variable (R A B)

/--
Instance `Algebra.IsIntegral.tensorProduct` / 实例 `Algebra.IsIntegral.tensorProduct`

English:
instance Algebra.IsIntegral.tensorProduct
  signature: [CommRing B]
  body: p.induction_on isIntegral_zero (fun _ s => .tmul _ <| int.1 s) (fun _ _ => .add)

中文:
实例 代数.是整.tensorProduct
  签名: [交换环 B]
  定义体: p.induction_on isIntegral_zero (fun _ s => .tmul _ <| int.1 s) (fun _ _ => .add)

Depends on / 依赖: induction_on, isIntegral_zero, p.induction_on
-/
instance Algebra.IsIntegral.tensorProduct [CommRing B]
    [Algebra R A] [Algebra R B] [int : Algebra.IsIntegral R B] :
    Algebra.IsIntegral A (A otimes[R] B) where
  isIntegral p := p.induction_on isIntegral_zero (fun _ s => .tmul _ <| int.1 s) (fun _ _ => .add)

end TensorProduct

section MulSemiringAction

variable {G R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [Group G] [MulSemiringAction G K] [SMulCommClass G R K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulSemiringAction G (integralClosure R K)
  body: fun g x => ⟨g • (x : K), x.2.map (MulSemiringAction.toAlgHom R K g)⟩
  one_smul x := by ext; exact one_smul G (x : K)
  mul_smul g h x := by ext; exact mul_smul g h (x : K)
  smul_zero g := by ext; exact smul_zero g
  smul_add g x y := by ext; exact smul_add g (x : K) (y : K)
  smul_one g := by ext; exact smul_one g
  smul_mul g x y := by ext; exact smul_mul' g (x : K) (y : K)

@[simp]

中文:
实例 :
  签名: MulSemiring作用 G (integralClosure R K)
  定义体: fun g x => ⟨g • (x : K), x.2.map (MulSemiringAction.toAlgHom R K g)⟩
  one_smul x := by ext; exact one_smul G (x : K)
  mul_smul g h x := by ext; exact mul_smul g h (x : K)
  smul_zero g := by ext; exact smul_zero g
  smul_add g x y := by ext; exact smul_add g (x : K) (y : K)
  smul_one g := by ext; exact smul_one g
  smul_mul g x y := by ext; exact smul_mul' g (x : K) (y : K)

@[simp]

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toAlgHom, toAlgHom
-/
instance : MulSemiringAction G (integralClosure R K) where
  smul := fun g x => ⟨g • (x : K), x.2.map (MulSemiringAction.toAlgHom R K g)⟩
  one_smul x := by ext; exact one_smul G (x : K)
  mul_smul g h x := by ext; exact mul_smul g h (x : K)
  smul_zero g := by ext; exact smul_zero g
  smul_add g x y := by ext; exact smul_add g (x : K) (y : K)
  smul_one g := by ext; exact smul_one g
  smul_mul g x y := by ext; exact smul_mul' g (x : K) (y : K)

@[simp]
/--
theorem `integralClosure.coe_smul` / 定理 `integralClosure.coe_smul`

English:
theorem integralClosure.coe_smul
  given: (g : G) (k : integralClosure R K)
  proof: rfl

中文:
定理 integralClosure.coe_smul
  条件: (g : G) (k : integralClosure R K)
  证明: rfl
-/
theorem integralClosure.coe_smul (g : G) (k : integralClosure R K) :
    (g • k : integralClosure R K) = g • (k : K) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass G R (integralClosure R K)
  body: Subtype.ext (smul_comm g r (k : K))

中文:
实例 :
  签名: 标量交换类 G R (integralClosure R K)
  定义体: Subtype.ext (smul_comm g r (k : K))

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance : SMulCommClass G R (integralClosure R K) where
  smul_comm g r k := Subtype.ext (smul_comm g r (k : K))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulDistribClass G (integralClosure R K) K
  body: smul_mul' g (r : K) k

中文:
实例 :
  签名: SMulDistrib类 G (integralClosure R K) K
  定义体: smul_mul' g (r : K) k

Depends on / 依赖: smul_mul
-/
instance : SMulDistribClass G (integralClosure R K) K where
  smul_distrib_smul g r k := smul_mul' g (r : K) k

end MulSemiringAction
