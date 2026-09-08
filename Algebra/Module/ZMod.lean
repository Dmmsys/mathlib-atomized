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

variable {n : ℕ} {M M₁ : Type*}

/-- The `ZMod n`-module structure on commutative monoids whose elements have order dividing `n ≠ 0`.
Also implies a group structure via `Module.addCommMonoidToAddCommGroup`.
See note [reducible non-instances]. -/
/-
**AddCommMonoid.zmodModule** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddCommMonoid.zmodModule [NeZero n] [AddCommMonoid M] (h : forall (x : M),
 n • x = 0) : Module (ZMod n) M
参数：h : forall (x : M), n • x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ZMod n`-module structure on commutative monoids whose elements have order d
ividing `n ≠ 0`.
Also implies a group structure via `Module.addCommMonoidToAddCommGroup`.
See note [reducible non-instances].
-/
abbrev AddCommMonoid.zmodModule [NeZero n] [AddCommMonoid M] (h : ∀ (x : M), n • x = 0) :
    Module (ZMod n) M := by
  have h_mod (c : ℕ) (x : M) : (c % n) • x = c • x := by
    suffices (c % n + c / n * n) • x = c • x by rwa [add_nsmul, mul_nsmul, h, add_zero] at this
    rw [Nat.mod_add_div']
  have := NeZero.ne n
  match n with
  | n + 1 => exact {
    smul := fun (c : Fin _) x ↦ c.val • x
    smul_zero := fun _ ↦ nsmul_zero _
    zero_smul := fun _ ↦ zero_nsmul _
    smul_add := fun _ _ _ ↦ nsmul_add _ _ _
    one_smul := fun _ ↦ (h_mod _ _).trans <| one_nsmul _
    add_smul := fun _ _ _ ↦ (h_mod _ _).trans <| add_nsmul _ _ _
    mul_smul := fun _ _ _ ↦ (h_mod _ _).trans <| mul_nsmul' _ _ _
  }

/-- The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`.
See note [reducible non-instances]. -/
/-
**AddCommGroup.zmodModule** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddCommGroup.zmodModule {G : Type*} [AddCommGroup G] (h : forall (x : G), 
n • x = 0) : Module (ZMod n) G
参数：h : forall (x : G), n • x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ZMod n`-module structure on Abelian groups whose elements have order dividi
ng `n`.
See note [reducible non-instances].
-/
abbrev AddCommGroup.zmodModule {G : Type*} [AddCommGroup G] (h : ∀ (x : G), n • x = 0) :
    Module (ZMod n) G :=
  match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

/-- The quotient of an abelian group by a subgroup containing all multiples of `n` is a
`n`-torsion group. -/
-- See note [reducible non-instances]
/-
**QuotientAddGroup.zmodModule** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：QuotientAddGroup.zmodModule {G : Type*} [AddCommGroup G] {H : AddSubgroup 
G} (hH : forall x, n • x in H) : Module (ZMod n) (G ⧸ H)
参数：hH : forall x, n • x in H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev QuotientAddGroup.zmodModule {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (hH : ∀ x, n • x ∈ H) : Module (ZMod n) (G ⧸ H) :=
  AddCommGroup.zmodModule <| by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

namespace ZMod

/-
**ZMod.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：map_smul (f : F) (c : ZMod n) (x : M) : f (c • x) = c • f x
参数：f : F；c : ZMod n；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
· 使用定理 `map_intCast_smul`：map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Rin
g R] […
-/
theorem map_smul (f : F) (c : ZMod n) (x : M) : f (c • x) = c • f x := by
  rw [← ZMod.intCast_zmod_cast c]
  exact map_intCast_smul f _ _ (cast c) x
/-
**ZMod.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：smul_mem (hx : x in K) (c : ZMod n) : c • x in K
参数：hx : x in K；c : ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
-/
theorem smul_mem (hx : x ∈ K) (c : ZMod n) : c • x ∈ K := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

end ZMod

variable (n)

namespace AddMonoidHom

/-- Reinterpret an additive homomorphism as a `ℤ/nℤ`-linear map.

See also:
`AddMonoidHom.toIntLinearMap`, `AddMonoidHom.toNatLinearMap`, `AddMonoidHom.toRatLinearMap` -/
/-
**AddMonoidHom.toZModLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：toZModLinearMap (f : M ->+ M₁) : M ->ₗ[ZMod n] M₁
参数：f : M ->+ M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an additive homomorphism as a `ℤ/nℤ`-linear map.

See also:
`AddMonoidHom.toIntLinearMap`, `AddMonoidHom.toNatLinearMap`, `AddMonoidHom.toRa
tLinearMap`
-/
def toZModLinearMap (f : M →+ M₁) : M →ₗ[ZMod n] M₁ := { f with map_smul' := ZMod.map_smul f }
/-
**AddMonoidHom.toZModLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom
`。
形式化陈述：toZModLinearMap_injective : Function.Injective toZModLinearMap n (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toZModLinearMap_injective : Function.Injective <| toZModLinearMap n (M := M) (M₁ := M₁) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

@[simp]
/-
**AddMonoidHom.coe_toZModLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：coe_toZModLinearMap (f : M ->+ M₁) : ⇑(f.toZModLinearMap n) = f
参数：f : M ->+ M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toZModLinearMap (f : M →+ M₁) : ⇑(f.toZModLinearMap n) = f := rfl

/-- `AddMonoidHom.toZModLinearMap` as an equivalence. -/
/-
**AddMonoidHom.toZModLinearMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：toZModLinearMapEquiv : (M ->+ M₁) ≃+ (M ->ₗ[ZMod n] M₁) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidHom.toZModLinearMap` as an equivalence.
-/
def toZModLinearMapEquiv : (M →+ M₁) ≃+ (M →ₗ[ZMod n] M₁) where
  toFun f := f.toZModLinearMap n
  invFun g := g
  map_add' f₁ f₂ := by ext; simp

end AddMonoidHom

namespace AddSubgroup

/-- Reinterpret an additive subgroup of a `ℤ/nℤ`-module as a `ℤ/nℤ`-submodule.

See also: `AddSubgroup.toIntSubmodule`, `AddSubmonoid.toNatSubmodule`. -/
/-
**AddSubgroup.toZModSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M where toFun S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an additive subgroup of a `ℤ/nℤ`-module as a `ℤ/nℤ`-submodule.

See also: `AddSubgroup.toIntSubmodule`, `AddSubmonoid.toNatSubmodule`.
-/
def toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M where
  toFun S := { S with smul_mem' := fun c _ h ↦ ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]
/-
**AddSubgroup.toZModSubmodule_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：toZModSubmodule_symm : ⇑((toZModSubmodule n).symm : _ ≃o AddSubgroup M) = 
Submodule.toAddSubgroup
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toZModSubmodule_symm :
    ⇑((toZModSubmodule n).symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl
/-
**AddSubgroup.coe_toZModSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：∀ (n : ℕ) {M : Type u_1} [inst : AddCommGroup M] [inst_1 : _root_.Module (
ZMod n) M] (S : AddSubgroup M),   ↑((AddSubgroup.toZModSubmodule n) S) = ↑S
参数：n : ℕ；ZMod n；S : AddSubgroup M；(AddSubgroup.toZModSubmodule n) S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toZModSubmodule (S : AddSubgroup M) : (toZModSubmodule n S : Set M) = S := rfl
/-
**AddSubgroup.mem_toZModSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：∀ (n : ℕ) {M : Type u_1} [inst : AddCommGroup M] [inst_1 : _root_.Module (
ZMod n) M] {x : M} {S : AddSubgroup M},   x ∈ (AddSubgroup.toZModSubmodule n) S 
↔ x ∈ S
参数：n : ℕ；ZMod n；AddSubgroup.toZModSubmodule n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_toZModSubmodule {S : AddSubgroup M} : x ∈ toZModSubmodule n S ↔ x ∈ S := .rfl

@[simp]
/-
**AddSubgroup.toZModSubmodule_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgro
up`。
形式化陈述：toZModSubmodule_toAddSubgroup (S : AddSubgroup M) : (toZModSubmodule n S).
toAddSubgroup = S
参数：S : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toZModSubmodule_toAddSubgroup (S : AddSubgroup M) :
    (toZModSubmodule n S).toAddSubgroup = S :=
  rfl

@[simp]
/-
**AddSubgroup._root_.Submodule.toAddSubgroup_toZModSubmodule** 是 Mathlib 中的一个定理，
位于命名空间 `AddSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.toAddSubgroup_toZModSubmodule (S : Submodule (ZMod n) M) :
    toZModSubmodule n S.toAddSubgroup = S :=
  rfl

end AddSubgroup

namespace ZModModule
variable {p : ℕ} {G : Type*} [AddCommGroup G]

/-- In an elementary abelian `p`-group, every finite subgroup `H` contains a further subgroup of
cardinality between `k` and `p * k`, if `k ≤ |H|`. -/
/-
**ZModModule.exists_submodule_subset_card_le** 是 Mathlib 中的一个引理，位于命名空间 `ZModModu
le`。
形式化陈述：exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G] (H : Su
bmodule (ZMod p) G) {k : Nat} (hk : k <= Nat.card H) (h'k : k != 0) : exists H' 
: Submodule (ZMod p) G, Nat.card H' <= k ∧ k < p * Nat.card H' ∧ H' <= H
参数：hp : p.Prime；ZMod p；H : Submodule (ZMod p) G；hk : k <= Nat.card H；h'k : k != 
0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sylow.exists_subgroup_le_card_le`：exists_subgroup_le_card_le {k p : Nat}
 (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G} (hk : k <= Nat.card H) (hk₀ 
: k != 0) : exists H' …
· 使用引理 `ZModModule.isPGroup_multiplicative`：isPGroup_multiplicative : IsPGroup n
 (Multiplicative G)

--- 原说明 ---
In an elementary abelian `p`-group, every finite subgroup `H` contains a further
 subgroup of
cardinality between `k` and `p * k`, if `k ≤ |H|`.
-/
lemma exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G]
    (H : Submodule (ZMod p) G) {k : ℕ} (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ H' : Submodule (ZMod p) G, Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

end ZModModule

