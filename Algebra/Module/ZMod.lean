/-
Copyright (c) 2023 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.GroupTheory.Sylow

/-!
# The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

variable {n : Nat} {M M₁ : Type*}

/--
Definition of `AddCommMonoid.zmodModule` / `AddCommMonoid.zmodModule` 的定义

English:
abbreviation AddCommMonoid.zmodModule
  signature: [NeZero n] [AddCommMonoid M] (h : forall (x : M), n • x = 0)
  body: by
  have h_mod (c : Nat) (x : M) : (c % n) • x = c • x := by
    suffices (c % n + c / n * n) • x = c • x by rwa [add_nsmul, mul_nsmul, h, add_zero] at this
    rw [Nat.mod_add_div']
  have := NeZero.ne n
  match n with
  | n + 1 => exact {
    smul := fun (c : Fin _) x => c.val • x
    smul_zero := fun _ => nsmul_zero _
    zero_smul := fun _ => zero_nsmul _
    smul_add := fun _ _ _ => nsmul_add _ _ _
one_smul := fun _ => (h_mod _ _).trans one_nsmul _
add_smul := fun _ _ _ => (h_mod _ _).trans add_nsmul _ _ _
mul_smul := fun _ _ _ => (h_mod _ _).trans mul_nsmul' _ _ _
  }

中文:
缩写 加法交换幺半群.zmodModule
  签名: [NeZero n] [加法交换幺半群 M] (h : 对任意 (x : M), n • x = 0)
  定义体: by
  have h_mod (c : Nat) (x : M) : (c % n) • x = c • x := by
    suffices (c % n + c / n * n) • x = c • x by rwa [add_nsmul, mul_nsmul, h, add_zero] at this
    rw [Nat.mod_add_div']
  have := NeZero.ne n
  match n with
  | n + 1 => exact {
    smul := fun (c : Fin _) x => c.val • x
    smul_zero := fun _ => nsmul_zero _
    zero_smul := fun _ => zero_nsmul _
    smul_add := fun _ _ _ => nsmul_add _ _ _
one_smul := fun _ => (h_mod _ _).trans one_nsmul _
add_smul := fun _ _ _ => (h_mod _ _).trans add_nsmul _ _ _
mul_smul := fun _ _ _ => (h_mod _ _).trans mul_nsmul' _ _ _
  }

Depends on / 依赖: Nat.mod_add_div, NeZero, NeZero.ne, add_nsmul, add_smul, add_zero, c.val, h_mod, mod_add_div, mul_nsmul, mul_smul, nsmul_add, nsmul_zero, one_nsmul, one_smul, smul_add, smul_zero, zero_nsmul, zero_smul
-/
abbrev AddCommMonoid.zmodModule [NeZero n] [AddCommMonoid M] (h : forall (x : M), n • x = 0) :
    Module (ZMod n) M := by
  have h_mod (c : Nat) (x : M) : (c % n) • x = c • x := by
    suffices (c % n + c / n * n) • x = c • x by rwa [add_nsmul, mul_nsmul, h, add_zero] at this
    rw [Nat.mod_add_div']
  have := NeZero.ne n
  match n with
  | n + 1 => exact {
    smul := fun (c : Fin _) x => c.val • x
    smul_zero := fun _ => nsmul_zero _
    zero_smul := fun _ => zero_nsmul _
    smul_add := fun _ _ _ => nsmul_add _ _ _
one_smul := fun _ => (h_mod _ _).trans one_nsmul _
add_smul := fun _ _ _ => (h_mod _ _).trans add_nsmul _ _ _
mul_smul := fun _ _ _ => (h_mod _ _).trans mul_nsmul' _ _ _
  }

/--
Definition of `AddCommGroup.zmodModule` / `AddCommGroup.zmodModule` 的定义

English:
abbreviation AddCommGroup.zmodModule
  signature: {G : Type*} [AddCommGroup G] (h : forall (x : G), n • x = 0)
  body: match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

中文:
缩写 加法交换群.zmodModule
  签名: {G : 类型} [加法交换群 G] (h : 对任意 (x : G), n • x = 0)
  定义体: match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

Depends on / 依赖: AddCommGroup, AddCommGroup.toIntModule, AddCommMonoid, AddCommMonoid.zmodModule, toIntModule, zmodModule
-/
abbrev AddCommGroup.zmodModule {G : Type*} [AddCommGroup G] (h : forall (x : G), n • x = 0) :
    Module (ZMod n) G :=
  match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

-- See note [reducible non-instances]
/--
Definition of `QuotientAddGroup.zmodModule` / `QuotientAddGroup.zmodModule` 的定义

English:
abbreviation QuotientAddGroup.zmodModule
  signature: {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
  body: AddCommGroup.zmodModule by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]

中文:
缩写 QuotientAddGroup.zmodModule
  签名: {G : 类型} [加法交换群 G] {H : 加法子群 G}
  定义体: AddCommGroup.zmodModule by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]

Depends on / 依赖: AddCommGroup, AddCommGroup.zmodModule, QuotientAddGroup, QuotientAddGroup.forall_mk, QuotientAddGroup.mk_nsmul, forall_mk, mk_nsmul, zmodModule
-/
abbrev QuotientAddGroup.zmodModule {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (hH : forall x, n • x in H) : Module (ZMod n) (G ⧸ H) :=
AddCommGroup.zmodModule by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

namespace ZMod

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : F) (c : ZMod n) (x : M)
  statement: f (c • x) = c • f x
  proof: by
  rw [← ZMod.intCast_zmod_cast c]
  exact map_intCast_smul f _ _ (cast c) x

中文:
定理 map_smul
  条件: (f : F) (c : ZMod n) (x : M)
  结论: f (c • x) = c • f x
  证明: by
  rw [← ZMod.intCast_zmod_cast c]
  exact map_intCast_smul f _ _ (cast c) x

Depends on / 依赖: ZMod.intCast_zmod_cast, intCast_zmod_cast, map_intCast_smul
-/
theorem map_smul (f : F) (c : ZMod n) (x : M) : f (c • x) = c • f x := by
  rw [← ZMod.intCast_zmod_cast c]
  exact map_intCast_smul f _ _ (cast c) x

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: (hx : x in K) (c : ZMod n)
  statement: c • x in K
  proof: by
  rw [← ZMod.intCast_zmod_cast c]; rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

中文:
定理 smul_mem
  条件: (hx : x in K) (c : ZMod n)
  结论: c • x in K
  证明: by
  rw [← ZMod.intCast_zmod_cast c]; rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

Depends on / 依赖: Int.cast_smul_eq_zsmul, ZMod.intCast_zmod_cast, cast_smul_eq_zsmul, intCast_zmod_cast, zsmul_mem
-/
theorem smul_mem (hx : x in K) (c : ZMod n) : c • x in K := by
  rw [← ZMod.intCast_zmod_cast c]; rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

end ZMod

variable (n)

namespace AddMonoidHom

/--
Definition of `toZModLinearMap` / `toZModLinearMap` 的定义

English:
definition toZModLinearMap
  signature: (f : M ->+ M₁)
  body: { f with map_smul' := ZMod.map_smul f }

中文:
定义 toZModLinearMap
  签名: (f : M ->+ M₁)
  定义体: { f with map_smul' := ZMod.map_smul f }

Depends on / 依赖: ZMod.map_smul, map_smul
-/
def toZModLinearMap (f : M ->+ M₁) : M ->ₗ[ZMod n] M₁ := { f with map_smul' := ZMod.map_smul f }

/--
theorem `toZModLinearMap_injective` / 定理 `toZModLinearMap_injective`

English:
theorem toZModLinearMap_injective
  statement: Function.Injective toZModLinearMap n (M := M) (M₁ := M₁)
  proof: fun _ _ h => ext fun x => congr($h x)

@[simp]

中文:
定理 toZModLinearMap_injective
  结论: 函数.单射 toZModLinearMap n (M := M) (M₁ := M₁)
  证明: fun _ _ h => ext fun x => congr($h x)

@[simp]
-/
theorem toZModLinearMap_injective : Function.Injective toZModLinearMap n (M := M) (M₁ := M₁) :=
  fun _ _ h => ext fun x => congr($h x)

@[simp]
/--
theorem `coe_toZModLinearMap` / 定理 `coe_toZModLinearMap`

English:
theorem coe_toZModLinearMap
  given: (f : M ->+ M₁)
  statement: ⇑(f.toZModLinearMap n) = f
  proof: rfl

中文:
定理 coe_toZModLinearMap
  条件: (f : M ->+ M₁)
  结论: ⇑(f.toZModLinearMap n) = f
  证明: rfl
-/
theorem coe_toZModLinearMap (f : M ->+ M₁) : ⇑(f.toZModLinearMap n) = f := rfl

/--
Definition of `toZModLinearMapEquiv` / `toZModLinearMapEquiv` 的定义

English:
definition toZModLinearMapEquiv
  signature: : (M ->+ M₁) ≃+ (M ->ₗ[ZMod n] M₁) where
  body: f.toZModLinearMap n
  invFun g := g
  map_add' f₁ f₂ := by ext; simp

中文:
定义 toZModLinearMapEquiv
  签名: : (M ->+ M₁) ≃+ (M ->ₗ[ZMod n] M₁) where
  定义体: f.toZModLinearMap n
  invFun g := g
  map_add' f₁ f₂ := by ext; simp

Depends on / 依赖: f.toZModLinearMap, toZModLinearMap
-/
def toZModLinearMapEquiv : (M ->+ M₁) ≃+ (M ->ₗ[ZMod n] M₁) where
  toFun f := f.toZModLinearMap n
  invFun g := g
  map_add' f₁ f₂ := by ext; simp

end AddMonoidHom

namespace AddSubgroup

/--
Definition of `toZModSubmodule` / `toZModSubmodule` 的定义

English:
definition toZModSubmodule
  signature: : AddSubgroup M ≃o Submodule (ZMod n) M where
  body: { S with smul_mem' := fun c _ h => ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 toZModSubmodule
  签名: : 加法子群 M ≃o 子模 (ZMod n) M where
  定义体: { S with smul_mem' := fun c _ h => ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]

Depends on / 依赖: ZMod.smul_mem, smul_mem
-/
def toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M where
  toFun S := { S with smul_mem' := fun c _ h => ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `toZModSubmodule_symm` / 定理 `toZModSubmodule_symm`

English:
theorem toZModSubmodule_symm
  proof: rfl

中文:
定理 toZModSubmodule_symm
  证明: rfl
-/
theorem toZModSubmodule_symm :
    ⇑((toZModSubmodule n).symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl

/--
lemma `coe_toZModSubmodule` / 引理 `coe_toZModSubmodule`

English:
lemma coe_toZModSubmodule
  given: (S : AddSubgroup M)
  statement: (toZModSubmodule n S : Set M) = S
  proof: rfl

中文:
引理 coe_toZModSubmodule
  条件: (S : 加法子群 M)
  结论: (toZModSubmodule n S : 集合 M) = S
  证明: rfl
-/
@[simp] lemma coe_toZModSubmodule (S : AddSubgroup M) : (toZModSubmodule n S : Set M) = S := rfl
/--
lemma `mem_toZModSubmodule` / 引理 `mem_toZModSubmodule`

English:
lemma mem_toZModSubmodule
  given: {S : AddSubgroup M}
  statement: x in toZModSubmodule n S ↔ x in S
  proof: .rfl

@[simp]

中文:
引理 mem_toZModSubmodule
  条件: {S : 加法子群 M}
  结论: x in toZModSubmodule n S ↔ x in S
  证明: .rfl

@[simp]
-/
@[simp] lemma mem_toZModSubmodule {S : AddSubgroup M} : x in toZModSubmodule n S ↔ x in S := .rfl

@[simp]
/--
theorem `toZModSubmodule_toAddSubgroup` / 定理 `toZModSubmodule_toAddSubgroup`

English:
theorem toZModSubmodule_toAddSubgroup
  given: (S : AddSubgroup M)
  proof: rfl

@[simp]

中文:
定理 toZModSubmodule_toAddSubgroup
  条件: (S : 加法子群 M)
  证明: rfl

@[simp]
-/
theorem toZModSubmodule_toAddSubgroup (S : AddSubgroup M) :
    (toZModSubmodule n S).toAddSubgroup = S :=
  rfl

@[simp]
/--
theorem `_root_.Submodule.toAddSubgroup_toZModSubmodule` / 定理 `_root_.Submodule.toAddSubgroup_toZModSubmodule`

English:
theorem _root_.Submodule.toAddSubgroup_toZModSubmodule
  given: (S : Submodule (ZMod n) M)
  proof: rfl

中文:
定理 _root_.子模.toAddSubgroup_toZModSubmodule
  条件: (S : 子模 (ZMod n) M)
  证明: rfl
-/
theorem _root_.Submodule.toAddSubgroup_toZModSubmodule (S : Submodule (ZMod n) M) :
    toZModSubmodule n S.toAddSubgroup = S :=
  rfl

end AddSubgroup

namespace ZModModule
variable {p : Nat} {G : Type*} [AddCommGroup G]

/--
lemma `exists_submodule_subset_card_le` / 引理 `exists_submodule_subset_card_le`

English:
lemma exists_submodule_subset_card_le
  statement: (hp : p.Prime) [Module (ZMod p) G]
  proof: by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

中文:
引理 存在_submodule_subset_card_le
  结论: (hp : p.素) [模 (ZMod p) G]
  证明: by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.toSubgroup, AddSubgroup.toSubgroup.symm, AddSubgroup.toZModSubmodule, Sylow.exists_subgroup_le_card_le, exists_subgroup_le_card_le, isPGroup_multiplicative, toSubgroup, toZModSubmodule
-/
lemma exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G]
    (H : Submodule (ZMod p) G) {k : Nat} (hk : k <= Nat.card H) (h'k : k != 0) :
    exists H' : Submodule (ZMod p) G, Nat.card H' <= k ∧ k < p * Nat.card H' ∧ H' <= H := by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

end ZModModule
