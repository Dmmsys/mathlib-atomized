/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Image of a hyperplane under inversion

In this file we prove that the inversion with center `c` and radius `R ≠ 0` maps a sphere passing
through the center to a hyperplane, and vice versa. More precisely, it maps a sphere with center
`y ≠ c` and radius `dist y c` to the hyperplane
`AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R y)`.

The exact statements are a little more complicated because `EuclideanGeometry.inversion c R` sends
the center to itself, not to a point at infinity.

We also prove that the inversion sends an affine subspace passing through the center to itself.

## Keywords

inversion
-/

public section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {c x y : P} {R : ℝ}

namespace EuclideanGeometry

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The inversion with center `c` and radius `R` maps a sphere passing through the center to a
hyperplane. -/
/-
**EuclideanGeometry.inversion_mem_perpBisector_inversion_iff** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：inversion_mem_perpBisector_inversion_iff (hR : R != 0) (hx : x != c) (hy :
 y != c) : inversion c R x in perpBisector c (inversion c R y) ↔ dist x y = dist
 y c
参数：hR : R != 0；hx : x != c；hy : y != c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_perpBisector_iff_dist_eq`：mem_perpBisector_iff_dist_e
q : c in perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂
· 使用定理 `EuclideanGeometry.dist_inversion_inversion`：dist_inversion_inversion (hx
 : x != c) (hy : y != c) (R : Real) : dist (inversion c R x) (inversion c R y) =
 R ^ 2 / (dist x c * dist y c) *…
· 使用定理 `EuclideanGeometry.dist_inversion_center`：dist_inversion_center (c x : P)
 (R : Real) : dist (inversion c R x) c = R ^ 2 / dist x c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The inversion with center `c` and radius `R` maps a sphere passing through the c
enter to a
hyperplane.
-/
theorem inversion_mem_perpBisector_inversion_iff (hR : R ≠ 0) (hx : x ≠ c) (hy : y ≠ c) :
    inversion c R x ∈ perpBisector c (inversion c R y) ↔ dist x y = dist y c := by
  rw [mem_perpBisector_iff_dist_eq, dist_inversion_inversion hx hy, dist_inversion_center]
  simp [field, eq_comm, ↓hx, ↓hy]

/-- The inversion with center `c` and radius `R` maps a sphere passing through the center to a
hyperplane. -/
/-
**EuclideanGeometry.inversion_mem_perpBisector_inversion_iff'** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：inversion_mem_perpBisector_inversion_iff' (hR : R != 0) (hy : y != c) : in
version c R x in perpBisector c (inversion c R y) ↔ dist x y = dist y c ∧ x != c
参数：hR : R != 0；hy : y != c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.inversion_self`：inversion_self (c : P) (R : Real) : in
version c R c = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `EuclideanGeometry.inversion_mem_perpBisector_inversion_iff`：inversion_me
m_perpBisector_inversion_iff (hR : R != 0) (hx : x != c) (hy : y != c) : inversi
on c R x in perpBisector c (inversion c R y) ↔ d…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
The inversion with center `c` and radius `R` maps a sphere passing through the c
enter to a
hyperplane.
-/
theorem inversion_mem_perpBisector_inversion_iff' (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R x ∈ perpBisector c (inversion c R y) ↔ dist x y = dist y c ∧ x ≠ c := by
  rcases eq_or_ne x c with rfl | hx
  · simp [*]
  · simp [inversion_mem_perpBisector_inversion_iff hR hx hy, hx]
/-
**EuclideanGeometry.preimage_inversion_perpBisector_inversion** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：preimage_inversion_perpBisector_inversion (hR : R != 0) (hy : y != c) : in
version c R ⁻¹' perpBisector c (inversion c R y) = sphere y (dist y c) \ {c}
参数：hR : R != 0；hy : y != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `EuclideanGeometry.inversion_mem_perpBisector_inversion_iff'`：inversion_m
em_perpBisector_inversion_iff' (hR : R != 0) (hy : y != c) : inversion c R x in 
perpBisector c (inversion c R y) ↔ dist x y = dis…
-/
theorem preimage_inversion_perpBisector_inversion (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R ⁻¹' perpBisector c (inversion c R y) = sphere y (dist y c) \ {c} :=
  Set.ext fun _ ↦ inversion_mem_perpBisector_inversion_iff' hR hy
/-
**EuclideanGeometry.preimage_inversion_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：preimage_inversion_perpBisector (hR : R != 0) (hy : y != c) : inversion c 
R ⁻¹' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c}
参数：hR : R != 0；hy : y != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.dist_inversion_center`：dist_inversion_center (c x : P)
 (R : Real) : dist (inversion c R x) c = R ^ 2 / dist x c
· 使用定理 `EuclideanGeometry.preimage_inversion_perpBisector_inversion`：preimage_in
version_perpBisector_inversion (hR : R != 0) (hy : y != c) : inversion c R ⁻¹' p
erpBisector c (inversion c R y) = sphere y (dist …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.inversion_inversion`：inversion_inversion (c : P) {R : 
Real} (hR : R != 0) (x : P) : inversion c R (inversion c R x) = x
-/
theorem preimage_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R ⁻¹' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  rw [← dist_inversion_center, ← preimage_inversion_perpBisector_inversion hR,
    inversion_inversion] <;> simp [*]
/-
**EuclideanGeometry.image_inversion_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：image_inversion_perpBisector (hR : R != 0) (hy : y != c) : inversion c R '
' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c}
参数：hR : R != 0；hy : y != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `EuclideanGeometry.inversion_involutive`：inversion_involutive (c : P) {R 
: Real} (hR : R != 0) : Involutive (inversion c R)
· 使用定理 `EuclideanGeometry.preimage_inversion_perpBisector`：preimage_inversion_pe
rpBisector (hR : R != 0) (hy : y != c) : inversion c R ⁻¹' perpBisector c y = sp
here (inversion c R y) (R ^ 2 / dist y …
-/
theorem image_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R '' perpBisector c y = sphere (inversion c R y) (R ^ 2 / dist y c) \ {c} := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR),
    preimage_inversion_perpBisector hR hy]
/-
**EuclideanGeometry.preimage_inversion_sphere_dist_center** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：preimage_inversion_sphere_dist_center (hR : R != 0) (hy : y != c) : invers
ion c R ⁻¹' sphere y (dist y c) = insert c (perpBisector c (inversion c R y) : S
et P)
参数：hR : R != 0；hy : y != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.inversion_self`：inversion_self (c : P) (R : Real) : in
version c R c = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Metric.mem_sphere`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α}
 {ε : ℝ}, y ∈ Metric.sphere x ε ↔ dist y x = ε
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.inversion_mem_perpBisector_inversion_iff`：inversion_me
m_perpBisector_inversion_iff (hR : R != 0) (hx : x != c) (hy : y != c) : inversi
on c R x in perpBisector c (inversion c R y) ↔ d…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.inversion_inversion`：inversion_inversion (c : P) {R : 
Real} (hR : R != 0) (x : P) : inversion c R (inversion c R x) = x
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem preimage_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R ⁻¹' sphere y (dist y c) =
      insert c (perpBisector c (inversion c R y) : Set P) := by
  ext x
  rcases eq_or_ne x c with rfl | hx; · simp [dist_comm]
  rw [mem_preimage, mem_sphere, ← inversion_mem_perpBisector_inversion_iff hR] <;> simp [*]
/-
**EuclideanGeometry.image_inversion_sphere_dist_center** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry`。
形式化陈述：image_inversion_sphere_dist_center (hR : R != 0) (hy : y != c) : inversion
 c R '' sphere y (dist y c) = insert c (perpBisector c (inversion c R y) : Set P
)
参数：hR : R != 0；hy : y != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `EuclideanGeometry.inversion_involutive`：inversion_involutive (c : P) {R 
: Real} (hR : R != 0) : Involutive (inversion c R)
· 使用定理 `EuclideanGeometry.preimage_inversion_sphere_dist_center`：preimage_invers
ion_sphere_dist_center (hR : R != 0) (hy : y != c) : inversion c R ⁻¹' sphere y 
(dist y c) = insert c (perpBisector c (invers…
-/
theorem image_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R '' sphere y (dist y c) = insert c (perpBisector c (inversion c R y) : Set P) := by
  rw [image_eq_preimage_of_inverse (inversion_involutive _ hR) (inversion_involutive _ hR),
    preimage_inversion_sphere_dist_center hR hy]

/-- Inversion sends an affine subspace passing through the center to itself. -/
/-
**EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：mapsTo_inversion_affineSubspace_of_mem {p : AffineSubspace Real P} (hp : c
 in p) : MapsTo (inversion c R) p p
参数：hp : c in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…

--- 原说明 ---
Inversion sends an affine subspace passing through the center to itself.
-/
theorem mapsTo_inversion_affineSubspace_of_mem {p : AffineSubspace ℝ P} (hp : c ∈ p) :
    MapsTo (inversion c R) p p := fun _ ↦ AffineMap.lineMap_mem _ hp

/-- Inversion sends an affine subspace passing through the center to itself. -/
/-
**EuclideanGeometry.image_inversion_affineSubspace_of_mem** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：image_inversion_affineSubspace_of_mem {p : AffineSubspace Real P} (hR : R 
!= 0) (hp : c in p) : inversion c R '' p = p
参数：hR : R != 0；hp : c in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem`：mapsTo_inversi
on_affineSubspace_of_mem {p : AffineSubspace Real P} (hp : c in p) : MapsTo (inv
ersion c R) p p
· 使用定理 `EuclideanGeometry.inversion_inversion`：inversion_inversion (c : P) {R : 
Real} (hR : R != 0) (x : P) : inversion c R (inversion c R x) = x

--- 原说明 ---
Inversion sends an affine subspace passing through the center to itself.
-/
theorem image_inversion_affineSubspace_of_mem {p : AffineSubspace ℝ P} (hR : R ≠ 0) (hp : c ∈ p) :
    inversion c R '' p = p :=
  (mapsTo_inversion_affineSubspace_of_mem hp).image_subset.antisymm fun x hx ↦
    ⟨inversion c R x, mapsTo_inversion_affineSubspace_of_mem hp hx, inversion_inversion _ hR _⟩

end EuclideanGeometry

