/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Lemmas about localizations of commutative monoids

that requires additional imports.
-/

public section

namespace Submonoid.IsLocalizationMap

open Finset in
/-- See also the analogous `IsLocalization.map_integerMultiple`. -/
/-
**Submonoid.IsLocalizationMap.surj_pi_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Submo
noid.IsLocalizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {F : Type u_3} {ι : Type u_4} [Finite ι] [
inst : CommMonoid M] [inst_1 : CommMonoid N]   [inst_2 : FunLike F M N] [MulHomC
lass F M N] {f : F} {S : Submonoid M},   S.IsLocalizationMap ⇑f → ∀ (n : ι → N),
 ∃ s x, ∀ (i : ι), n i * f ↑s = f (x i)
参数：n : ι → N；i : ι；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
See also the analogous `IsLocalization.map_integerMultiple`.
-/
@[to_additive] theorem surj_pi_of_finite {M N F ι : Type*} [Finite ι]
    [CommMonoid M] [CommMonoid N] [FunLike F M N] [MulHomClass F M N] {f : F}
    {S : Submonoid M} (hf : IsLocalizationMap S f) (n : ι → N) :
    ∃ (s : S) (x : ι → M), ∀ i, n i * f s = f (x i) := by
  choose x hx using hf.surj
  have ⟨_⟩ := nonempty_fintype ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i ↦ (x (n i)).1 * ∏ j ∈ univ.erase i, (x (n j)).2, fun i ↦ ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i), S.coe_mul, map_mul, ← mul_assoc, hx, map_mul]
/-
**Submonoid.IsLocalizationMap.pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsLocaliza
tionMap`。
形式化陈述：∀ {ι : Type u_1} {M : ι → Type u_2} {N : ι → Type u_3} [inst : (i : ι) → C
ommMonoid (M i)]   [inst_1 : (i : ι) → CommMonoid (N i)] (S : (i : ι) → Submonoi
d (M i)) {f : (i : ι) → M i → N i},   (∀ (i : ι), (S i).IsLocalizationMap (f i))
 → (Submonoid.pi Set.univ S).IsLocalizationMap (Pi.map f)
参数：i : ι；M i；i : ι；N i；S : (i : ι) → Submonoid (M i)；i : ι；∀ (i : ι), (S i).IsLo
calizationMap (f i)；Submonoid.pi Set.univ S；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Pi.isUnit_iff`：Pi.isUnit_iff : IsUnit x ↔ forall i, IsUnit (x i)
· 使用定理 `Submonoid.IsLocalizationMap.map_units`：∀ {M : Type u_1} [inst : CommMono
id M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.
IsLocalizationMap f → ∀ (y …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
@[to_additive] protected theorem pi {ι : Type*} {M N : ι → Type*}
    [∀ i, CommMonoid (M i)] [∀ i, CommMonoid (N i)] (S : Π i, Submonoid (M i))
    {f : Π i, M i → N i} (hf : ∀ i, IsLocalizationMap (S i) (f i)) :
    IsLocalizationMap (Submonoid.pi .univ S) (Pi.map f) where
  map_units m := Pi.isUnit_iff.mpr fun i ↦ (hf i).map_units ⟨_, m.2 i ⟨⟩⟩
  surj z := by
    choose x hx using fun i ↦ (hf i).surj
    exact ⟨⟨fun i ↦ (x i (z i)).1, ⟨_, fun i _ ↦ (x i (z i)).2.2⟩⟩, funext fun i ↦ hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i ↦ (hf i).exists_of_eq congr($eq i)
    exact ⟨⟨_, fun i _ ↦ (c i).2⟩, funext hc⟩

end Submonoid.IsLocalizationMap

