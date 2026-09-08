/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.ordHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
cheme`。
形式化陈述：ordHom (z : X) (hz : coheight z = 1) : X.functionField ->*₀ Intᵐ⁰
参数：z : X；hz : coheight z = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfI
sLocallyNoetherian`：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocall
yNoetherian X] {x : ↥X},   IsNoetherianRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunct
ionField`：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsIntegral 
X] (x : ↥X),   IsFractionRing ↑(X.presheaf.stalk x) ↑X.functionField
-/
def ordHom (z : X) (hz : coheight z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)
/-
**AlgebraicGeometry.Scheme.ordHom_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：ordHom_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) 
{x : X} (hx : coheight x = 1) (hx' : x in U) : ordHom x hx (X.germToFunctionFiel
d U f) = 1
参数：X, U；hf : IsUnit f；hx : coheight x = 1；hx' : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.krullDimLE_of_coheight_le`：krullDimLE_of_coheight_le {
z : X} {n : Nat} (hz : coheight z <= n) : Ring.KrullDimLE n (X.presheaf.stalk z)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField`：∀ (X : 
AlgebraicGeometry.Scheme) [inst : IrreducibleSpace ↥X] {U : X.Opens} [inst_1 : N
onempty ↥↑U] {x : ↥X}   (hx : x ∈ U) (f : ↑(X.preshea…
· 使用引理 `Ring.ordFrac_of_isUnit`：ordFrac_of_isUnit {x : R} (hx : IsUnit x) : ordF
rac R (algebraMap R K x) = 1
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegra
l`：∀ (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsIntegral X] {x : ↥X}, I
sDomain ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfI
sLocallyNoetherian`：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocall
yNoetherian X] {x : ↥X},   IsNoetherianRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunct
ionField`：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsIntegral 
X] (x : ↥X),   IsFractionRing ↑(X.presheaf.stalk x) ↑X.functionField
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point. This has a junk value of `0` if `f = 0` or if `coheight z ≠ 1`.
-/
@[no_expose]
noncomputable
/-
**AlgebraicGeometry.Scheme.ord** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sche
me`。
形式化陈述：ord (f : X.functionField) (z : X) : Int
参数：f : X.functionField；z : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ord (f : X.functionField) (z : X) : ℤ :=
  if hz : coheight z = 1
  then Multiplicative.toAdd <| (X.ordHom z hz f).unzeroD 1
  else 0
/-
**AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.func
tionField) : ord f z = Multiplicative.toAdd ((X.ordHom z hz f).unzeroD 1)
参数：hz : coheight z = 1；f : X.functionField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) :
    ord f z = Multiplicative.toAdd ((X.ordHom z hz f).unzeroD 1) := dif_pos hz

@[simp]
/-
**AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.func
tionField) : ord f z = 0
参数：hz : coheight z != 1；f : X.functionField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z ≠ 1) (f : X.functionField) :
    ord f z = 0 := dif_neg hz

@[simp]
/-
**AlgebraicGeometry.Scheme.ord_zero** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
.Scheme`。
形式化陈述：ord_zero : ord (0 : X.functionField) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one`：ord_eq_ordHom
_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) : ord f 
z = Multiplicative.toAdd ((X.ordHom z hz f).unz…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`：ord_eq_zero_of
_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) : ord f z
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma ord_zero : ord (0 : X.functionField) = 0 := by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]
/-
**AlgebraicGeometry.Scheme.ord_eq_unzero_ordHom** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (
hf : f != 0) : ord f x = (WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).
toAdd
参数：hx : coheight x = 1；hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `WithZero.unzeroD_eq_unzero`：∀ {α : Type u} {d : α} {x : WithZero α} (hx 
: x ≠ 0), WithZero.unzeroD d x = WithZero.unzero hx
-/
lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f ≠ 0) :
    ord f x = (WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).toAdd := by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]
/-
**AlgebraicGeometry.Scheme.ord_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f != 
0) {n : Int} : ord f z = n ↔ ordHom z hz f = Multiplicative.ofAdd n
参数：hz : coheight z = 1；hf : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_unzero_ordHom`：ord_eq_unzero_ordHom {x :
 X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0) : ord f x = (WithZ
ero.unzero ((map_ne_zero (ordHom x …
· 使用引理 `WithZero.toAdd_unzero_eq_iff`：toAdd_unzero_eq_iff {α : Type*} {a : WithZ
ero (Multiplicative α)} (h : a != 0) (b : α) : (WithZero.unzero h).toAdd = b ↔ a
 = Multiplicative.…
-/
lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) {n : ℤ} :
    ord f z = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]
/-
**AlgebraicGeometry.Scheme.ord_mul** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：ord_mul {x : X} {f g : X.functionField} (hf : f != 0) (hg : g != 0) : ord 
(f * g) x = ord f x + ord g x
参数：hf : f != 0；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`：ord_eq_zero_of
_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) : ord f z
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_iff`：ord_eq_iff {z : X} (hz : coheight z
 = 1) {f : X.functionField} (hf : f != 0) {n : Int} : ord f z = n ↔ ordHom z hz 
f = Multiplicative.ofAdd …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_ne_zero_iff_right`：mul_ne_zero_iff_right (hb : b != 0) : a * b != 0 
↔ a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegra
l`：∀ (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsIntegral X] {x : ↥X}, I
sDomain ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one`：ord_eq_ordHom
_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) : ord f 
z = Multiplicative.toAdd ((X.ordHom z hz f).unz…
· 使用定理 `WithZero.unzeroD_eq_unzero`：∀ {α : Type u} {d : α} {x : WithZero α} (hx 
: x ≠ 0), WithZero.unzeroD d x = WithZero.unzero hx
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
-/
lemma ord_mul {x : X} {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) : ord (f * g) x = ord f x + ord g x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]
/-
**AlgebraicGeometry.Scheme.ord_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x 
: X} (hx' : x in U) : ord (X.germToFunctionField U f) x = 0
参数：X, U；hf : IsUnit f；hx' : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`：ord_eq_zero_of
_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) : ord f z
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_iff`：ord_eq_iff {z : X} (hz : coheight z
 = 1) {f : X.functionField} (hf : f != 0) {n : Int} : ord f z = n ↔ ordHom z hz 
f = Multiplicative.ofAdd …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `AlgebraicGeometry.Scheme.component_nontrivial`：∀ (X : AlgebraicGeometry.
Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial ↑(X.presheaf.obj (Opposite.op U
))
· 使用引理 `AlgebraicGeometry.Scheme.ordHom_of_isUnit`：ordHom_of_isUnit {U : X.Opens
} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' 
: x in U) : ordHom x hx (X.germ…
-/
lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx' : x ∈ U) : ord (X.germToFunctionField U f) x = 0 := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']
/-
**AlgebraicGeometry.Scheme.ord_le_ord_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g 
: X.functionField} (hf : f != 0) (hg : g != 0) : ord f x <= ord g y ↔ ordHom x h
x f <= ordHom y hy g
参数：hx : coheight x = 1；hy : coheight y = 1；hf : f != 0；hg : g != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_unzero_ordHom`：ord_eq_unzero_ordHom {x :
 X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0) : ord f x = (WithZ
ero.unzero ((map_ne_zero (ordHom x …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord f x ≤ ord g y ↔ ordHom x hx f ≤ ordHom y hy g := by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]
/-
**AlgebraicGeometry.Scheme.le_ord_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 
0) {n : Int} : n <= ord f x ↔ Multiplicative.ofAdd n <= ordHom x hx f
参数：hx : coheight x = 1；hf : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_unzero_ordHom`：ord_eq_unzero_ordHom {x :
 X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0) : ord f x = (WithZ
ero.unzero ((map_ne_zero (ordHom x …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toAdd_ofAdd`：toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x
· 使用定理 `Multiplicative.toAdd_le`：toAdd_le {a b : Multiplicative α} : a.toAdd <= 
b.toAdd ↔ a <= b
· 使用引理 `WithZero.le_unzero_iff`：le_unzero_iff (hy : y != 0) : a <= unzero hy ↔ a
 <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField}
    (hf : f ≠ 0) {n : ℤ} :
    n ≤ ord f x ↔ Multiplicative.ofAdd n ≤ ordHom x hx f := by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le, le_unzero_iff]
/-
**AlgebraicGeometry.Scheme.ord_add** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：ord_add {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)] {f g : X.fu
nctionField} (hfg : f + g != 0) : min (ord f x) (ord g x) <= ord (f + g) x
参数：X.presheaf.stalk x；hfg : f + g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegra
l`：∀ (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsIntegral X] {x : ↥X}, I
sDomain ↑(X.presheaf.stalk x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.ord.congr_simp`：∀ {X : AlgebraicGeometry.Scheme
} [inst : AlgebraicGeometry.IsIntegral X]   [inst_1 : AlgebraicGeometry.IsLocall
yNoetherian X] (f f_1 : ↑X.fu…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.ord_zero`：ord_zero : ord (0 : X.functionField) 
= 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`：ord_eq_zero_of
_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) : ord f z
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `inf_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.ord_le_ord_iff`：ord_le_ord_iff {x y : X} (hx : 
coheight x = 1) (hy : coheight y = 1) {f g : X.functionField} (hf : f != 0) (hg 
: g != 0) : ord f x <= ord g …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.ordFrac_add`：ordFrac_add (x y : K) (h1 : x + y != 0) : min (Ring.or
dFrac R x) (Ring.ordFrac R y) <= Ring.ordFrac R (x + y)
· 使用定理 `AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunct
ionField`：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsIntegral 
X] (x : ↥X),   IsFractionRing ↑(X.presheaf.stalk x) ↑X.functionField
-/
lemma ord_add {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (hfg : f + g ≠ 0) :
    min (ord f x) (ord g x) ≤ ord (f + g) x := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [inf_le_iff, ord_le_ord_iff hx hx hf hfg, ord_le_ord_iff hx hx hg hfg]
  exact inf_le_iff.mp <| Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg
/-
**AlgebraicGeometry.Scheme.ord_le_smul** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：ord_le_smul {x : X} {U : X.Opens} [Nonempty U] (hxU : x in U) {a : Γ(X, U)
} (ha : a != 0) (f : X.functionField) : ord f x <= ord (a • f) x
参数：hxU : x in U；X, U；ha : a != 0；f : X.functionField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`：ord_eq_zero_of
_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) : ord f z
 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AlgebraicGeometry.Scheme.ord.congr_simp`：∀ {X : AlgebraicGeometry.Scheme
} [inst : AlgebraicGeometry.IsIntegral X]   [inst_1 : AlgebraicGeometry.IsLocall
yNoetherian X] (f f_1 : ↑X.fu…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.ord_zero`：ord_zero : ord (0 : X.functionField) 
= 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegra
l`：∀ (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsIntegral X] {x : ↥X}, I
sDomain ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `AlgebraicGeometry.Scheme.ord_le_ord_iff`：ord_le_ord_iff {x y : X} (hx : 
coheight x = 1) (hy : coheight y = 1) {f g : X.functionField} (hf : f != 0) (hg 
: g != 0) : ord f x <= ord g …
· 使用引理 `AlgebraicGeometry.krullDimLE_of_coheight_le`：krullDimLE_of_coheight_le {
z : X} {n : Nat} (hz : coheight z <= n) : Ring.KrullDimLE n (X.presheaf.stalk z)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfI
sLocallyNoetherian`：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocall
yNoetherian X] {x : ↥X},   IsNoetherianRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunct
ionField`：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsIntegral 
X] (x : ↥X),   IsFractionRing ↑(X.presheaf.stalk x) ↑X.functionField
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma ord_le_smul {x : X} {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    {a : Γ(X, U)} (ha : a ≠ 0) (f : X.functionField) : ord f x ≤ ord (a • f) x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f ≠ 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU).hom]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  simp [ordHom, Ring.ordFrac_le_smul, RingHom.algebraMap_toAlgebra, map_ne_zero_iff,
    germ_injective_of_isIntegral, ha]

end AlgebraicGeometry.Scheme

