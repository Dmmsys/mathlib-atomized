/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.OreLocalization.NonZeroDivisors

/-!

# Module and Ring instances of Ore Localizations

The `Monoid` and `DistribMulAction` instances and additive versions are provided in
`Mathlib/RingTheory/OreLocalization/Basic.lean`.

-/

@[expose] public section

assert_not_exists Subgroup

universe u

namespace OreLocalization

section Module

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [Module R X]

/-
**OreLocalization.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Submonoid R} [inst_1 : OreLocali
zation.OreSet S] {X : Type u_2}   [inst_2 : AddCommMonoid X] [inst_3 : _root_.Mo
dule R X] (x : OreLocalization S X), 0 • x = 0
参数：x : OreLocalization S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `OreLocalization.oreDiv_smul_char`：oreDiv_smul_char (r₁ : R) (r₂ : X) (s₁
 s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) : (r₁ /ₒ s₁) • (r₂ /ₒ s₂) =
 r' • r₂ /ₒ (s' * s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
-/
protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def, oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp
/-
**OreLocalization.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Submonoid R} [inst_1 : OreLocali
zation.OreSet S] {X : Type u_2}   [inst_2 : AddCommMonoid X] [inst_3 : _root_.Mo
dule R X] (y z : OreLocalization S R) (x : OreLocalization S X),   (y + z) • x =
 y • x + z • x
参数：y z : OreLocalization S R；x : OreLocalization S X；y + z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.expand'`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] (r : X) (…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `OreLocalization.expand`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoi
d R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R 
X] (r : X) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_eq_of_eq_mk`：coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h :
 ↑a = b) : a = ⟨b, h ▸ a.2⟩
· 使用定理 `OreLocalization.oreDiv_add_char`：oreDiv_add_char {r r' : X} (s s' : S) (
rb : R) (sb : S) (h : sb * s = rb * s') : r /ₒ s + r' /ₒ s' = (sb • r + rb • r')
 /ₒ (sb * s)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `OreLocalization.smul_cancel'`：∀ {R : Type u_1} [inst : Monoid R] {S : Su
bmonoid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAct
ion R X] {r₁ : R} …
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
protected theorem add_smul (y z : R[S⁻¹]) (x : X[S⁻¹]) :
    (y + z) • x = y • x + z • x := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ ∈ S := by
    rw [mul_assoc, ← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc, hb, mul_assoc, ← mul_assoc _ ra, hc, ← mul_assoc, ← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]

end Module

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

attribute [local instance] OreLocalization.oreEqv

/-
**OreLocalization.left_distrib** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Submonoid R} [inst_1 : OreLocali
zation.OreSet S]   (x y z : OreLocalization S R), x * (y + z) = x * y + x * z
参数：x y z : OreLocalization S R；y + z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.smul_add`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid 
X] [inst_3 : D…
-/
protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
  OreLocalization.smul_add _ _ _
/-
**OreLocalization.right_distrib** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z
参数：x y z : R[S⁻¹]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.add_smul`：∀ {R : Type u_1} [inst : Semiring R] {S : Subm
onoid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddCommM
onoid X] [inst…
-/
theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
  OreLocalization.add_smul _ _ _
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring R[S⁻¹] where
  __ := (inferInstance : MonoidWithZero (R[S⁻¹]))
  __ := (inferInstance : AddCommMonoid (R[S⁻¹]))
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

variable {X : Type*} [AddCommMonoid X] [Module R X]
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R[S⁻¹] X[S⁻¹] where
  add_smul := OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [Semiring R₀] [Module R₀ X] [Module R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    Module R₀ X[S⁻¹] where
  add_smul r s x := by simp only [← smul_one_oreDiv_one_smul, add_smul, ← add_oreDiv]
  zero_smul x := by rw [← smul_one_oreDiv_one_smul, zero_smul, zero_oreDiv, zero_smul]

@[simp]
/-
**OreLocalization.nsmul_eq_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `OreLocalization`。
形式化陈述：nsmul_eq_nsmul (n : Nat) (x : X[S⁻¹]) : letI inst
参数：n : Nat；x : X[S⁻¹]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
lemma nsmul_eq_nsmul (n : ℕ) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℕ) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℕ) (R := R) (X := X) (S := S)
  exact congr($(AddCommMonoid.uniqueNatModule.2 inst).smul n x)

/-- The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /ₒ 1`. -/
@[simps!]
/-
**OreLocalization.numeratorRingHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `OreLocalization`
。
形式化陈述：numeratorRingHom : R ->+* R[S⁻¹] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /
ₒ 1`.
-/
abbrev numeratorRingHom : R →+* R[S⁻¹] where
  __ := numeratorHom
  map_zero' := by with_unfolding_all exact OreLocalization.zero_def
  map_add' _ _ := add_oreDiv.symm
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommSemiring R₀] [Algebra R₀ R] : Algebra R₀ R[S⁻¹] where
  __ := (inferInstance : Module R₀ R[S⁻¹])
  algebraMap := numeratorRingHom.comp (algebraMap R₀ R)
  commutes' r x := by
    induction x using OreLocalization.ind with | _ r₁ s₁
    dsimp
    rw [mul_div_one, oreDiv_mul_char _ _ _ _ (algebraMap R₀ R r) s₁ (Algebra.commutes _ _).symm,
      Algebra.commutes, mul_one]
  smul_def' r x := by
    dsimp
    rw [Algebra.algebraMap_eq_smul_one, ← smul_eq_mul, smul_one_oreDiv_one_smul]

section UMP

variable {T : Type*} [Semiring T]
variable (f : R →+* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
/-
**OreLocalization.universalHom** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：universalHom : R[S⁻¹] ->+* T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal lift from a ring homomorphism `f : R →+* T`, which maps elements i
n `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the constructi
on on
monoids.
-/
def universalHom : R[S⁻¹] →+* T :=
  { universalMulHom f.toMonoidHom fS hf with
    map_zero' := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [OreLocalization.zero_def, universalMulHom_apply]
      simp
    map_add' := fun x y => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      induction x with | _ r₁ s₁
      induction y with | _ r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, map_mul, map_add, map_mul, Units.val_mul]
      rw [mul_add, mul_assoc, ← mul_assoc _ (f s₃), hf, ← Units.val_mul]
      simp only [one_mul, inv_mul_cancel, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul, ← mul_inv_rev, ← fS.map_mul, h₃']
      rw [Units.inv_mul_eq_iff_eq_mul, Units.eq_mul_inv_iff_mul_eq, ← hf, ← hf]
      simp only [map_mul] }
/-
**OreLocalization.universalHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`
。
形式化陈述：universalHom_apply {r : R} {s : S} : universalHom f fS hf (r /ₒ s) = ((fS 
s)⁻¹ : Units T) * f r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl
/-
**OreLocalization.universalHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalizati
on`。
形式化陈述：universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f 
r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]
/-
**OreLocalization.universalHom_unique** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization
`。
形式化陈述：universalHom_unique (φ : R[S⁻¹] ->+* T) (huniv : forall r : R, φ (numerato
rHom r) = f r) : φ = universalHom f fS hf
参数：φ : R[S⁻¹] ->+* T；huniv : forall r : R, φ (numeratorHom r) = f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_monoidHom_injective`：coe_monoidHom_injective : Injective (fu
n f : α ->+* β => (f : α ->* β))
· 使用定理 `OreLocalization.universalMulHom_unique`：universalMulHom_unique (φ : R[S⁻
¹] ->* T) (huniv : forall r : R, φ (numeratorHom r) = f r) : φ = universalMulHom
 f fS hf
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem universalHom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
  RingHom.coe_monoidHom_injective <| universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

end UMP

end Semiring

section Ring

variable {R : Type*} [Ring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [Module R X]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring R[S⁻¹] where
  __ := (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : AddGroup R[S⁻¹])

@[simp]
/-
**OreLocalization.zsmul_eq_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `OreLocalization`。
形式化陈述：zsmul_eq_zsmul (n : Int) (x : X[S⁻¹]) : letI inst
参数：n : Int；x : X[S⁻¹]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
lemma zsmul_eq_zsmul (n : ℤ) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℤ) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℤ) (R := R) (X := X) (S := S)
  exact congr($(AddCommGroup.uniqueIntModule.2 inst).smul n x)

open nonZeroDivisors
/-
**OreLocalization.numeratorHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：numeratorHom_inj (hS : S <= nonZeroDivisorsLeft R) : Function.Injective (n
umeratorHom : R -> R[S⁻¹])
参数：hS : S <= nonZeroDivisorsLeft R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `OreLocalization.numeratorHom_apply`：numeratorHom_apply {r : R} : numerat
orHom r = r /ₒ (1 : S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem numeratorHom_inj (hS : S ≤ nonZeroDivisorsLeft R) :
    Function.Injective (numeratorHom : R → R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂, ← sub_eq_zero, ← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

variable {R : Type*} [Ring R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivisionRing R[R⁰⁻¹] where
  mul_inv_cancel := OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end DivisionRing

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Submonoid R} [OreSet S]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring R[S⁻¹] where
  __ := (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {S : Submonoid R} [OreSet S]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing R[S⁻¹] where
  __ := (inferInstance : Ring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommRing

section Field

open nonZeroDivisors

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

noncomputable
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Field R[R⁰⁻¹] where
  __ := (inferInstance : DivisionRing R[R⁰⁻¹])
  __ := (inferInstance : CommMonoid R[R⁰⁻¹])

end Field

end OreLocalization

