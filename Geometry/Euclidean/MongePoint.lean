/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.Circumcenter

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `mongePoint` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `mongePlane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

* `OrthocentricSystem` is a predicate on sets of points that says
  whether they are four points, one of which is the orthocenter of the
  other three (in which case various other properties hold, including
  that each is the orthocenter of the other three).

## References

* <https://en.wikipedia.org/wiki/Monge_point>
* <https://en.wikipedia.org/wiki/Orthocentric_system>
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry PointsWithCircumcenterIndex

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1): 2.
Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
/-
**Affine.Simplex.mongePoint** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePoint {n : Nat} (s : Simplex Real P n) : P
参数：s : Simplex Real P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1): 2.
Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection.
-/
def mongePoint {n : ℕ} (s : Simplex ℝ P n) : P :=
  (((n + 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) •
      ((univ : Finset (Fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
/-
**Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Simplex`。
形式化陈述：mongePoint_eq_smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n)
 : s.mongePoint = (((n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)) • ((univ : F
inset (Fin (n + 1))).centroid Real s.points -ᵥ s.circumcenter) +ᵥ s.circumcenter
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The position of the Monge point in relation to the circumcenter
and centroid.
-/
theorem mongePoint_eq_smul_vsub_vadd_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.mongePoint =
      (((n + 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) •
          ((univ : Finset (Fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
        s.circumcenter :=
  rfl
/-
**Affine.Simplex.mongePoint_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} (s : Affine.Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)),   (s.reinde
x e).mongePoint = s.mongePoint
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.circumcenter_reindex`：circumcenter_reindex {m n : Nat} (s
 : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).circumcente
r = s.circumcenter
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.univ_map_embedding`：Finset.univ_map_embedding {α : Type*} [Fintyp
e α] (e : α ↪ α) : univ.map e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
-/
@[simp] lemma mongePoint_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).mongePoint = s.mongePoint := by
  simp_rw [mongePoint, circumcenter_reindex, centroid_def, reindex]
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  congr 3
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Affine.Simplex.mongePoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 
Real V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : Nat} (s : Simplex Real P 
n) (f : P ->ᵃⁱ[Real] P₂) : (s.map f.toAffineMap f.injective).mongePoint = f s.mo
ngePoint
参数：s : Simplex Real P n；f : P ->ᵃⁱ[Real] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.centroid.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module
 k V] [inst_3 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Affine.Simplex.centroid_map`：centroid_map [CharZero k] {V₂ P₂ : Type*} [
AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] {n : Nat} (s : Simplex k P n)
 (f : P ->ᵃ[k] P₂…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `Affine.Simplex.circumcenter_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
· 使用定理 `AffineIsometry.map_vadd`：map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linea
rIsometry v +ᵥ f p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `AffineIsometry.map_vsub`：map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ 
p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mongePoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).mongePoint = f s.mongePoint := by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter]
  rw [← Simplex.centroid, ← Simplex.centroid]
  simp [centroid_map, circumcenter_map]

/-- **Sylvester's theorem**: The position of the Monge point relative to the circumcenter via the
sum of vectors to the vertices. -/
/-
**Affine.Simplex.smul_mongePoint_vsub_circumcenter_eq_sum_vsub** 是 Mathlib 中的一个定
理，位于命名空间 `Affine.Simplex`。
形式化陈述：smul_mongePoint_vsub_circumcenter_eq_sum_vsub {n : Nat} (s : Simplex Real 
P (n + 2)) : (n + 1) • (s.mongePoint -ᵥ s.circumcenter) = ∑ i, (s.points i -ᵥ s.
circumcenter)
参数：s : Simplex Real P (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter`：mongePoint_eq_
smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n) : s.mongePoint = ((
(n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)…
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
**Sylvester's theorem**: The position of the Monge point relative to the circumc
enter via the
sum of vectors to the vertices.
-/
theorem smul_mongePoint_vsub_circumcenter_eq_sum_vsub {n : ℕ} (s : Simplex ℝ P (n + 2)) :
    (n + 1) • (s.mongePoint -ᵥ s.circumcenter) = ∑ i, (s.points i -ᵥ s.circumcenter) := by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter, vadd_vsub, ← smul_assoc]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.add_one_sub_one, nsmul_eq_mul]
  field_simp
  have h : Invertible (n + 2 + 1 : ℝ) := by norm_cast; apply invertibleOfPos
  rw [smul_eq_iff_eq_invOf_smul, smul_sum]
  rw [univ_centroid_eq, centroid_eq_affineCombination]
  rw [← Finset.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ (by simp)]
  simp only [centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, invOf_eq_inv]

/-- The Monge point lies in the affine span. -/
/-
**Affine.Simplex.mongePoint_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：mongePoint_mem_affineSpan {n : Nat} (s : Simplex Real P n) : s.mongePoint 
in affineSpan Real (Set.range s.points)
参数：s : Simplex Real P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `centroid_mem_affineSpan_of_card_eq_add_one`：centroid_mem_affineSpan_of_c
ard_eq_add_one [CharZero k] {s : Finset ι} (p : ι -> P) {n : Nat} (h : #s = n + 
1) : s.centroid k p in affineSpa…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)

--- 原说明 ---
The Monge point lies in the affine span.
-/
theorem mongePoint_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.mongePoint ∈ affineSpan ℝ (Set.range s.points) :=
  smul_vsub_vadd_mem _ _ (centroid_mem_affineSpan_of_card_eq_add_one ℝ _ (card_fin (n + 1)))
    s.circumcenter_mem_affineSpan s.circumcenter_mem_affineSpan

@[simp]
/-
**Affine.Simplex.mongePoint_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePoint_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace R
eal P) (hS : affineSpan Real (Set.range s.points) <= S) : haveI
参数：s : Simplex Real P n；S : AffineSubspace Real P；hS : affineSpan Real (Set.rang
e s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.centroid.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module
 k V] [inst_3 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Affine.Simplex.centroid_restrict`：centroid_restrict [CharZero k] {n : Na
t} (s : Simplex k P n) (S : AffineSubspace k P) (hS : affineSpan k (Set.range s.
points) <= S) : haveI
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Affine.Simplex.circumcenter_restrict`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mongePoint_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).mongePoint = s.mongePoint := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  simp_rw [mongePoint]
  rw [← Simplex.centroid, ← Simplex.centroid]
  simp [centroid_restrict, circumcenter_restrict]

/-- Two simplices with the same points have the same Monge point. -/
/-
**Affine.Simplex.mongePoint_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：mongePoint_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex Real P n} (h : Set.ra
nge s₁.points = Set.range s₂.points) : s₁.mongePoint = s₂.mongePoint
参数：h : Set.range s₁.points = Set.range s₂.points。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_eq_of_range_eq`：centroid_eq_of_range_eq {n : Nat
} {s₁ s₂ : Simplex k P n} (h : Set.range s₁.points = Set.range s₂.points) : Fins
et.univ.centroid k s₁.points…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.circumcenter_eq_of_range_eq`：circumcenter_eq_of_range_eq 
{n : Nat} {s₁ s₂ : Simplex Real P n} (h : Set.range s₁.points = Set.range s₂.poi
nts) : s₁.circumcenter = s₂.circ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two simplices with the same points have the same Monge point.
-/
theorem mongePoint_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex ℝ P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.mongePoint = s₂.mongePoint := by
  simp_rw [mongePoint_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
    circumcenter_eq_of_range_eq h]

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`pointsWithCircumcenter`. -/
/-
**Affine.Simplex.mongePointWeightsWithCircumcenter** 是 Mathlib 中的一个定义，位于命名空间 `Af
fine.Simplex`。
形式化陈述：(n : ℕ) → Affine.Simplex.PointsWithCircumcenterIndex (n + 2) → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the Monge point of an (n+2)-simplex, in terms of
`pointsWithCircumcenter`.
-/
def mongePointWeightsWithCircumcenter (n : ℕ) : PointsWithCircumcenterIndex (n + 2) → ℝ
  | pointIndex _ => ((n + 1 : ℕ) : ℝ)⁻¹
  | circumcenterIndex => -2 / ((n + 1 : ℕ) : ℝ)

/-- `mongePointWeightsWithCircumcenter` sums to 1. -/
@[simp]
/-
**Affine.Simplex.sum_mongePointWeightsWithCircumcenter** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：sum_mongePointWeightsWithCircumcenter (n : Nat) : ∑ i, mongePointWeightsWi
thCircumcenter n i = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
`mongePointWeightsWithCircumcenter` sums to 1.
-/
theorem sum_mongePointWeightsWithCircumcenter (n : ℕ) :
    ∑ i, mongePointWeightsWithCircumcenter n i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, mongePointWeightsWithCircumcenter, sum_const, card_fin,
    nsmul_eq_mul]
  simp [field]
  ring

/-- The Monge point of an (n+2)-simplex, in terms of
`pointsWithCircumcenter`. -/
/-
**Affine.Simplex.mongePoint_eq_affineCombination_of_pointsWithCircumcenter** 是 M
athlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : S
implex Real P (n + 2)) : s.mongePoint = (univ : Finset (PointsWithCircumcenterIn
dex (n + 2))).affineCombination Real s.pointsWithCircumcenter (mongePointWeights
WithCircumcenter n)
参数：s : Simplex Real P (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter`：mongePoint_eq_
smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n) : s.mongePoint = ((
(n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)…
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination_of_pointsWithCircumcenter`：
centroid_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex R
eal P n) (fs : Finset (Fin (n + 1))) : fs.centroid Real s.po…
· 使用定理 `Affine.Simplex.circumcenter_eq_affineCombination_of_pointsWithCircumcent
er`：circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : S
implex Real P n) : s.circumcenter = (univ : Finset (PointsWithCi…
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 112 条，此处仅展示前 30 条）

--- 原说明 ---
The Monge point of an (n+2)-simplex, in terms of
`pointsWithCircumcenter`.
-/
theorem mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P (n + 2)) :
    s.mongePoint =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).affineCombination ℝ
        s.pointsWithCircumcenter (mongePointWeightsWithCircumcenter n) := by
  rw [mongePoint_eq_smul_vsub_vadd_circumcenter,
    centroid_eq_affineCombination_of_pointsWithCircumcenter,
    circumcenter_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub, ← map_smul,
    weightedVSub_vadd_affineCombination]
  congr with i
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  cases i <;>
      simp_rw [centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
        mongePointWeightsWithCircumcenter] <;>
    rw [add_tsub_assoc_of_le (by decide : 1 ≤ 2), (by decide : 2 - 1 = 1)]
  · rw [if_pos (mem_univ _), card_fin]
    field
  · simp [field]
    ring

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`pointsWithCircumcenter`.  This definition is only valid when `i₁ ≠ i₂`. -/
/-
**Affine.Simplex.mongePointVSubFaceCentroidWeightsWithCircumcenter** 是 Mathlib 中
的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：{n : ℕ} → Fin (n + 3) → Fin (n + 3) → Affine.Simplex.PointsWithCircumcente
rIndex (n + 2) → ℝ
参数：n + 3；n + 3；n + 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`pointsWithCircumcenter`.  This definition is only valid when `i₁ ≠ i₂`.
-/
def mongePointVSubFaceCentroidWeightsWithCircumcenter {n : ℕ} (i₁ i₂ : Fin (n + 3)) :
    PointsWithCircumcenterIndex (n + 2) → ℝ
  | pointIndex i => if i = i₁ ∨ i = i₂ then ((n + 1 : ℕ) : ℝ)⁻¹ else 0
  | circumcenterIndex => -2 / ((n + 1 : ℕ) : ℝ)

/-- `mongePointVSubFaceCentroidWeightsWithCircumcenter` is the
result of subtracting `centroidWeightsWithCircumcenter` from
`mongePointWeightsWithCircumcenter`. -/
/-
**Affine.Simplex.mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub** 是 Ma
thlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub {n : Nat} {i₁ i₂ 
: Fin (n + 3)} (h : i₁ != i₂) : mongePointVSubFaceCentroidWeightsWithCircumcente
r i₁ i₂ = mongePointWeightsWithCircumcenter n - centroidWeightsWithCircumcenter 
{i₁, i₂}ᶜ
参数：n + 3；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Affine.Simplex.mongePointWeightsWithCircumcenter.eq_1`：∀ (n : ℕ) (a : Fi
n (n + 2 + 1)),   Affine.Simplex.mongePointWeightsWithCircumcenter n (Affine.Sim
plex.PointsWithCircumcenterIndex.pointIndex…
· 使用定理 `Affine.Simplex.centroidWeightsWithCircumcenter.eq_1`：∀ {n : ℕ} (fs : Fin
set (Fin (n + 1))) (a : Fin (n + 1)),   Affine.Simplex.centroidWeightsWithCircum
center fs (Affine.Simplex.PointsWithCircu…
· 使用定理 `Affine.Simplex.mongePointVSubFaceCentroidWeightsWithCircumcenter.eq_1`：∀
 {n : ℕ} (i₁ i₂ : Fin (n + 3)) (a : Fin (n + 2 + 1)),   Affine.Simplex.mongePoin
tVSubFaceCentroidWeightsWithCircumcenter i₁ i₂       (Affin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
`mongePointVSubFaceCentroidWeightsWithCircumcenter` is the
result of subtracting `centroidWeightsWithCircumcenter` from
`mongePointWeightsWithCircumcenter`.
-/
theorem mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub {n : ℕ} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ ≠ i₂) :
    mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂ =
      mongePointWeightsWithCircumcenter n - centroidWeightsWithCircumcenter {i₁, i₂}ᶜ := by
  ext i
  obtain i | i := i
  · rw [Pi.sub_apply, mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]
    have hu : #{i₁, i₂}ᶜ = n + 1 := by
      simp [card_compl, Fintype.card_fin, h]
    rw [hu]
    by_cases hi : i = i₁ ∨ i = i₂ <;> simp [compl_eq_univ_sdiff, hi]
  · simp [mongePointWeightsWithCircumcenter, centroidWeightsWithCircumcenter,
      mongePointVSubFaceCentroidWeightsWithCircumcenter]

/-- `mongePointVSubFaceCentroidWeightsWithCircumcenter` sums to 0. -/
@[simp]
/-
**Affine.Simplex.sum_mongePointVSubFaceCentroidWeightsWithCircumcenter** 是 Mathl
ib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：sum_mongePointVSubFaceCentroidWeightsWithCircumcenter {n : Nat} {i₁ i₂ : F
in (n + 3)} (h : i₁ != i₂) : ∑ i, mongePointVSubFaceCentroidWeightsWithCircumcen
ter i₁ i₂ i = 0
参数：n + 3；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub`
：mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub {n : Nat} {i₁ i₂ : Fin
 (n + 3)} (h : i₁ != i₂) : mongePointVSubFaceCentroidWeightsW…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Affine.Simplex.sum_mongePointWeightsWithCircumcenter`：sum_mongePointWeig
htsWithCircumcenter (n : Nat) : ∑ i, mongePointWeightsWithCircumcenter n i = 1
· 使用定理 `Affine.Simplex.sum_centroidWeightsWithCircumcenter`：sum_centroidWeightsW
ithCircumcenter {n : Nat} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty) : ∑ i, c
entroidWeightsWithCircumcenter fs i = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
`mongePointVSubFaceCentroidWeightsWithCircumcenter` sums to 0.
-/
theorem sum_mongePointVSubFaceCentroidWeightsWithCircumcenter {n : ℕ} {i₁ i₂ : Fin (n + 3)}
    (h : i₁ ≠ i₂) : ∑ i, mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂ i = 0 := by
  rw [mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]
  simp_rw [Pi.sub_apply, sum_sub_distrib, sum_mongePointWeightsWithCircumcenter]
  rw [sum_centroidWeightsWithCircumcenter, sub_self]
  simp [← card_pos, card_compl, h]

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCirc
umcenter** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter {n
 : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} (h : i₁ != i₂) : s.mo
ngePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s.points = (univ : 
Finset (PointsWithCircumcenterIndex (n + 2))).weightedVSub s.pointsWithCircumcen
ter (mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂)
参数：s : Simplex Real P (n + 2)；n + 3；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePoint_eq_affineCombination_of_pointsWithCircumcenter
`：mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simpl
ex Real P (n + 2)) : s.mongePoint = (univ : Finset (PointsWith…
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination_of_pointsWithCircumcenter`：
centroid_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex R
eal P n) (fs : Finset (Fin (n + 1))) : fs.centroid Real s.po…
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub`
：mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub {n : Nat} {i₁ i₂ : Fin
 (n + 3)} (h : i₁ != i₂) : mongePointVSubFaceCentroidWeightsW…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `pointsWithCircumcenter`.
-/
theorem mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} (h : i₁ ≠ i₂) :
    s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points =
      (univ : Finset (PointsWithCircumcenterIndex (n + 2))).weightedVSub s.pointsWithCircumcenter
        (mongePointVSubFaceCentroidWeightsWithCircumcenter i₁ i₂) := by
  simp_rw [mongePoint_eq_affineCombination_of_pointsWithCircumcenter,
    centroid_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub,
    mongePointVSubFaceCentroidWeightsWithCircumcenter_eq_sub h]

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
/-
**Affine.Simplex.inner_mongePoint_vsub_face_centroid_vsub** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Simplex`。
形式化陈述：inner_mongePoint_vsub_face_centroid_vsub {n : Nat} (s : Simplex Real P (n 
+ 2)) {i₁ i₂ : Fin (n + 3)} : ⟪s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))
).centroid Real s.points, s.points i₁ -ᵥ s.points i₂⟫ = 0
参数：s : Simplex Real P (n + 2)；n + 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `Affine.Simplex.mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWi
thCircumcenter`：mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircu
mcenter {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} (h : i₁…
· 使用定理 `Affine.Simplex.point_eq_affineCombination_of_pointsWithCircumcenter`：poi
nt_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.points i = (univ : Finset (Point…
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Affine.Simplex.sum_pointWeightsWithCircumcenter`：sum_pointWeightsWithCir
cumcenter {n : Nat} (i : Fin (n + 1)) : ∑ j, pointWeightsWithCircumcenter i j = 
1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.inner_weightedVSub`：inner_weightedVSub {ι₁ : Type*} {s
₁ : Finset ι₁} {w₁ : ι₁ -> Real} (p₁ : ι₁ -> P) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ :
 Type*} {s₂ : Finset ι₂} {…
· 使用定理 `Affine.Simplex.sum_mongePointVSubFaceCentroidWeightsWithCircumcenter`：su
m_mongePointVSubFaceCentroidWeightsWithCircumcenter {n : Nat} {i₁ i₂ : Fin (n + 
3)} (h : i₁ != i₂) : ∑ i, mongePointVSubFaceCentroidWeight…
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `Affine.Simplex.pointsWithCircumcenter_eq_circumcenter`：pointsWithCircumc
enter_eq_circumcenter {n : Nat} (s : Simplex Real P n) : s.pointsWithCircumcente
r circumcenterIndex = s.circumcenter
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face.
-/
theorem inner_mongePoint_vsub_face_centroid_vsub {n : ℕ} (s : Simplex ℝ P (n + 2))
    {i₁ i₂ : Fin (n + 3)} :
    ⟪s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points,
        s.points i₁ -ᵥ s.points i₂⟫ =
      0 := by
  by_cases h : i₁ = i₂
  · simp [h]
  simp_rw [mongePoint_vsub_face_centroid_eq_weightedVSub_of_pointsWithCircumcenter s h,
    point_eq_affineCombination_of_pointsWithCircumcenter, affineCombination_vsub]
  have hs : ∑ i, (pointWeightsWithCircumcenter i₁ - pointWeightsWithCircumcenter i₂) i = 0 := by
    simp
  rw [inner_weightedVSub _ (sum_mongePointVSubFaceCentroidWeightsWithCircumcenter h) _ hs,
    sum_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter]
  simp only [mongePointVSubFaceCentroidWeightsWithCircumcenter, pointsWithCircumcenter_point]
  let fs : Finset (Fin (n + 3)) := {i₁, i₂}
  have hfs : ∀ i : Fin (n + 3), i ∉ fs → i ≠ i₁ ∧ i ≠ i₂ := by
    intro i hi
    constructor <;> · intro hj; simp [fs, ← hj] at hi
  rw [← sum_subset fs.subset_univ _]
  · simp_rw [sum_pointsWithCircumcenter, pointsWithCircumcenter_eq_circumcenter,
      pointsWithCircumcenter_point, Pi.sub_apply, pointWeightsWithCircumcenter]
    rw [← sum_subset fs.subset_univ _]
    · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
      repeat rw [← sum_subset fs.subset_univ _]
      · simp_rw [fs, sum_insert (notMem_singleton.2 h), sum_singleton]
        simp [h, Ne.symm h, dist_comm (s.points i₁)]
      all_goals intro i _ hi; simp [hfs i hi]
    · intro i _ hi
      simp [hfs i hi]
  · intro i _ hi
    simp [hfs i hi]

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
/-
**Affine.Simplex.mongePlane** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePlane {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3)) : 
AffineSubspace Real P
参数：s : Simplex Real P (n + 2)；i₁ i₂ : Fin (n + 3)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`.
-/
def mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) : AffineSubspace ℝ P :=
  mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points) (ℝ ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
    affineSpan ℝ (Set.range s.points)

/-- The definition of a Monge plane. -/
/-
**Affine.Simplex.mongePlane_def** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePlane_def {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3)
) : s.mongePlane i₁ i₂ = mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid Real s
.points) (Real ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ affineSpan Real (Set.range s.p
oints)
参数：s : Simplex Real P (n + 2)；i₁ i₂ : Fin (n + 3)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of a Monge plane.
-/
theorem mongePlane_def {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ =
      mk' (({i₁, i₂}ᶜ : Finset (Fin (n + 3))).centroid ℝ s.points)
          (ℝ ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl
/-
**Affine.Simplex.mongePlane_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePlane_reindex {m n : Nat} (s : Simplex Real P (n + 2)) (e : Fin (n + 
3) ≃ Fin (m + 3)) (i₁ i₂ : Fin (m + 3)) : (s.reindex e).mongePlane i₁ i₂ = s.mon
gePlane (e.symm i₁) (e.symm i₂)
参数：s : Simplex Real P (n + 2)；e : Fin (n + 3) ≃ Fin (m + 3)；i₁ i₂ : Fin (m + 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.reindex_range_points`：reindex_range_points {m n : Nat} (s
 : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Set.range (s.reindex e).poin
ts = Set.range s.points
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `Finset.map_erase`：map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (
a : α) : (s.erase a).map f = (s.map f).erase (f a)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 31 条，此处仅展示前 30 条）
-/
lemma mongePlane_reindex {m n : ℕ} (s : Simplex ℝ P (n + 2)) (e : Fin (n + 3) ≃ Fin (m + 3))
    (i₁ i₂ : Fin (m + 3)) :
    (s.reindex e).mongePlane i₁ i₂ = s.mongePlane (e.symm i₁) (e.symm i₂) := by
  obtain rfl : n = m := by simpa using Fintype.card_eq.2 ⟨e⟩
  simp_rw [mongePlane, reindex_points, reindex_range_points, Function.comp_apply, centroid_def,
    reindex]
  congr 2
  convert! Finset.affineCombination_map {e.symm i₁, e.symm i₂}ᶜ e.toEmbedding _ _ using 3
  · ext i
    simp
  · simp [Function.comp_assoc]
  · simp_rw [centroidWeights, Function.const_comp, Finset.card_compl]
    congr 4
    by_cases h : i₁ = i₂ <;> simp [h]

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
/-
**Affine.Simplex.mongePlane_comm** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mongePlane_comm {n : Nat} (s : Simplex Real P (n + 2)) (i₁ i₂ : Fin (n + 3
)) : s.mongePlane i₁ i₂ = s.mongePlane i₂ i₁
参数：s : Simplex Real P (n + 2)；i₁ i₂ : Fin (n + 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pair_comm`：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁

--- 原说明 ---
The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`.
-/
theorem mongePlane_comm {n : ℕ} (s : Simplex ℝ P (n + 2)) (i₁ i₂ : Fin (n + 3)) :
    s.mongePlane i₁ i₂ = s.mongePlane i₂ i₁ := by
  simp_rw [mongePlane_def]
  congr 3
  · congr 1
    exact pair_comm _ _
  · ext
    simp_rw [Submodule.mem_span_singleton]
    constructor
    all_goals rintro ⟨r, rfl⟩; use -r; rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]

/-- The Monge point lies in the Monge planes. -/
/-
**Affine.Simplex.mongePoint_mem_mongePlane** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：mongePoint_mem_mongePlane {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : 
Fin (n + 3)} : s.mongePoint in s.mongePlane i₁ i₂
参数：s : Simplex Real P (n + 2)；n + 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePlane_def`：mongePlane_def {n : Nat} (s : Simplex Rea
l P (n + 2)) (i₁ i₂ : Fin (n + 3)) : s.mongePlane i₁ i₂ = mk' (({i₁, i₂}ᶜ : Fins
et (Fin (n + 3))).c…
· 使用定理 `AffineSubspace.mem_inf_iff`：mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace 
k P) : p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Affine.Simplex.inner_mongePoint_vsub_face_centroid_vsub`：inner_mongePoin
t_vsub_face_centroid_vsub {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n
 + 3)} : ⟪s.mongePoint -ᵥ ({i₁, i₂}ᶜ : Finset…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Affine.Simplex.mongePoint_mem_affineSpan`：mongePoint_mem_affineSpan {n :
 Nat} (s : Simplex Real P n) : s.mongePoint in affineSpan Real (Set.range s.poin
ts)

--- 原说明 ---
The Monge point lies in the Monge planes.
-/
theorem mongePoint_mem_mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    s.mongePoint ∈ s.mongePlane i₁ i₂ := by
  rw [mongePlane_def, mem_inf_iff, ← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _),
    direction_mk', Submodule.mem_orthogonal']
  refine ⟨?_, s.mongePoint_mem_affineSpan⟩
  intro v hv
  rcases Submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
  rw [inner_smul_right, s.inner_mongePoint_vsub_face_centroid_vsub, mul_zero]

/-- The direction of a Monge plane. -/
/-
**Affine.Simplex.direction_mongePlane** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：direction_mongePlane {n : Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (
n + 3)} : (s.mongePlane i₁ i₂).direction = (Real ∙ (s.points i₁ -ᵥ s.points i₂))
ᗮ ⊓ vectorSpan Real (Set.range s.points)
参数：s : Simplex Real P (n + 2)；n + 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePlane_def`：mongePlane_def {n : Nat} (s : Simplex Rea
l P (n + 2)) (i₁ i₂ : Fin (n + 3)) : s.mongePlane i₁ i₂ = mk' (({i₁, i₂}ᶜ : Fins
et (Fin (n + 3))).c…
· 使用定理 `AffineSubspace.direction_inf_of_mem_inf`：direction_inf_of_mem_inf {s₁ s₂
 : AffineSubspace k P} {p : P} (h : p in s₁ ⊓ s₂) : (s₁ ⊓ s₂).direction = s₁.dir
ection ⊓ s₂.direction
· 使用定理 `Affine.Simplex.mongePoint_mem_mongePlane`：mongePoint_mem_mongePlane {n :
 Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} : s.mongePoint in s.mon
gePlane i₁ i₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of a Monge plane.
-/
theorem direction_mongePlane {n : ℕ} (s : Simplex ℝ P (n + 2)) {i₁ i₂ : Fin (n + 3)} :
    (s.mongePlane i₁ i₂).direction =
      (ℝ ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) := by
  rw [mongePlane_def, direction_inf_of_mem_inf s.mongePoint_mem_mongePlane, direction_mk',
    direction_affineSpan]

/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
/-
**Affine.Simplex.eq_mongePoint_of_forall_mem_mongePlane** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Simplex`。
形式化陈述：eq_mongePoint_of_forall_mem_mongePlane {n : Nat} {s : Simplex Real P (n + 
2)} {i₁ : Fin (n + 3)} {p : P} (h : forall i₂, i₁ != i₂ -> p in s.mongePlane i₁ 
i₂) : p = s.mongePoint
参数：n + 2；n + 3；h : forall i₂, i₁ != i₂ -> p in s.mongePlane i₁ i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Affine.Simplex.direction_mongePlane`：direction_mongePlane {n : Nat} (s :
 Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} : (s.mongePlane i₁ i₂).direction 
= (Real ∙ (s.points i₁ -ᵥ…
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `Affine.Simplex.mongePoint_mem_mongePlane`：mongePoint_mem_mongePlane {n :
 Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} : s.mongePoint in s.mon
gePlane i₁ i₂
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The Monge point is the only point in all the Monge planes from any
one vertex.
-/
theorem eq_mongePoint_of_forall_mem_mongePlane {n : ℕ} {s : Simplex ℝ P (n + 2)} {i₁ : Fin (n + 3)}
    {p : P} (h : ∀ i₂, i₁ ≠ i₂ → p ∈ s.mongePlane i₁ i₂) : p = s.mongePoint := by
  rw [← @vsub_eq_zero_iff_eq V]
  have h' : ∀ i₂, i₁ ≠ i₂ → p -ᵥ s.mongePoint ∈
      (ℝ ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) := by
    intro i₂ hne
    rw [← s.direction_mongePlane, vsub_right_mem_direction_iff_mem s.mongePoint_mem_mongePlane]
    exact h i₂ hne
  have hi : p -ᵥ s.mongePoint ∈ ⨅ i₂ : { i // i₁ ≠ i }, (ℝ ∙ (s.points i₁ -ᵥ s.points i₂))ᗮ := by
    rw [Submodule.mem_iInf]
    exact fun i => (Submodule.mem_inf.1 (h' i i.property)).1
  rw [Submodule.iInf_orthogonal, ← Submodule.span_iUnion] at hi
  have hu :
    ⋃ i : { i // i₁ ≠ i }, ({s.points i₁ -ᵥ s.points i} : Set V) =
      (s.points i₁ -ᵥ ·) '' s.points '' (Set.univ \ {i₁}) := by
    rw [Set.image_image]
    ext x
    simp_rw [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_sdiff_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      use i, ⟨Set.mem_univ _, i.property.symm⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      use ⟨i, hi.symm⟩
  rw [hu, ← vectorSpan_image_eq_span_vsub_set_left_ne ℝ _ (Set.mem_univ _), Set.image_univ] at hi
  have hv : p -ᵥ s.mongePoint ∈ vectorSpan ℝ (Set.range s.points) := by
    let s₁ : Finset (Fin (n + 3)) := univ.erase i₁
    obtain ⟨i₂, h₂⟩ := card_pos.1 (show 0 < #s₁ by simp [s₁, card_erase_of_mem])
    have h₁₂ : i₁ ≠ i₂ := (ne_of_mem_erase h₂).symm
    exact (Submodule.mem_inf.1 (h' i₂ h₁₂)).2
  exact Submodule.disjoint_def.1 (vectorSpan ℝ (Set.range s.points)).orthogonal_disjoint _ hv hi

end Simplex

namespace Triangle

open EuclideanGeometry Finset Simplex AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
/-
**Affine.Triangle.orthocenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Triangle`。
形式化陈述：orthocenter (t : Triangle Real P) : P
参数：t : Triangle Real P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point.
-/
def orthocenter (t : Triangle ℝ P) : P :=
  t.mongePoint

/-- The orthocenter equals the Monge point. -/
/-
**Affine.Triangle.orthocenter_eq_mongePoint** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Tr
iangle`。
形式化陈述：orthocenter_eq_mongePoint (t : Triangle Real P) : t.orthocenter = t.mongeP
oint
参数：t : Triangle Real P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthocenter equals the Monge point.
-/
theorem orthocenter_eq_mongePoint (t : Triangle ℝ P) : t.orthocenter = t.mongePoint :=
  rfl
/-
**Affine.Triangle.orthocenter_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Triangle
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
t : Affine.Triangle ℝ P) (e : Fin 3 ≃ Fin 3),   Affine.Triangle.orthocenter (Aff
ine.Simplex.reindex t e) = t.orthocenter
参数：t : Affine.Triangle ℝ P；e : Fin 3 ≃ Fin 3；Affine.Simplex.reindex t e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.mongePoint_reindex`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
-/
@[simp] lemma orthocenter_reindex (t : Triangle ℝ P) (e : Fin 3 ≃ Fin 3) :
    orthocenter (t.reindex e) = t.orthocenter :=
  t.mongePoint_reindex e

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
/-
**Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Triangle`。
形式化陈述：orthocenter_eq_smul_vsub_vadd_circumcenter (t : Triangle Real P) : t.ortho
center = (3 : Real) • ((univ : Finset (Fin 3)).centroid Real t.points -ᵥ t.circu
mcenter : V) +ᵥ t.circumcenter
参数：t : Triangle Real P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter`：mongePoint_eq_
smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n) : s.mongePoint = ((
(n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The position of the orthocenter in relation to the circumcenter
and centroid.
-/
theorem orthocenter_eq_smul_vsub_vadd_circumcenter (t : Triangle ℝ P) :
    t.orthocenter =
      (3 : ℝ) • ((univ : Finset (Fin 3)).centroid ℝ t.points -ᵥ t.circumcenter : V) +ᵥ
        t.circumcenter := by
  rw [orthocenter_eq_mongePoint, mongePoint_eq_smul_vsub_vadd_circumcenter]
  simp

/-- **Sylvester's theorem**, specialized to triangles. -/
/-
**Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub** 是 Mathlib 中的一个定理，位
于命名空间 `Affine.Triangle`。
形式化陈述：orthocenter_vsub_circumcenter_eq_sum_vsub (t : Triangle Real P) : t.orthoc
enter -ᵥ t.circumcenter = ∑ i, (t.points i -ᵥ t.circumcenter)
参数：t : Triangle Real P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.smul_mongePoint_vsub_circumcenter_eq_sum_vsub`：smul_monge
Point_vsub_circumcenter_eq_sum_vsub {n : Nat} (s : Simplex Real P (n + 2)) : (n 
+ 1) • (s.mongePoint -ᵥ s.circumcenter) = ∑ i, (s.…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint

--- 原说明 ---
**Sylvester's theorem**, specialized to triangles.
-/
theorem orthocenter_vsub_circumcenter_eq_sum_vsub (t : Triangle ℝ P) :
    t.orthocenter -ᵥ t.circumcenter = ∑ i, (t.points i -ᵥ t.circumcenter) := by
  rw [← t.smul_mongePoint_vsub_circumcenter_eq_sum_vsub, zero_add, one_smul,
    orthocenter_eq_mongePoint]

/-- The orthocenter lies in the affine span. -/
/-
**Affine.Triangle.orthocenter_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 `Affine.T
riangle`。
形式化陈述：orthocenter_mem_affineSpan (t : Triangle Real P) : t.orthocenter in affine
Span Real (Set.range t.points)
参数：t : Triangle Real P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.mongePoint_mem_affineSpan`：mongePoint_mem_affineSpan {n :
 Nat} (s : Simplex Real P n) : s.mongePoint in affineSpan Real (Set.range s.poin
ts)

--- 原说明 ---
The orthocenter lies in the affine span.
-/
theorem orthocenter_mem_affineSpan (t : Triangle ℝ P) :
    t.orthocenter ∈ affineSpan ℝ (Set.range t.points) :=
  t.mongePoint_mem_affineSpan

/-- Two triangles with the same points have the same orthocenter. -/
/-
**Affine.Triangle.orthocenter_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.T
riangle`。
形式化陈述：orthocenter_eq_of_range_eq {t₁ t₂ : Triangle Real P} (h : Set.range t₁.poi
nts = Set.range t₂.points) : t₁.orthocenter = t₂.orthocenter
参数：h : Set.range t₁.points = Set.range t₂.points。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.mongePoint_eq_of_range_eq`：mongePoint_eq_of_range_eq {n :
 Nat} {s₁ s₂ : Simplex Real P n} (h : Set.range s₁.points = Set.range s₂.points)
 : s₁.mongePoint = s₂.mongePoi…

--- 原说明 ---
Two triangles with the same points have the same orthocenter.
-/
theorem orthocenter_eq_of_range_eq {t₁ t₂ : Triangle ℝ P}
    (h : Set.range t₁.points = Set.range t₂.points) : t₁.orthocenter = t₂.orthocenter :=
  mongePoint_eq_of_range_eq h

/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
/-
**Affine.Triangle.altitude_eq_mongePlane** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Trian
gle`。
形式化陈述：altitude_eq_mongePlane (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ 
!= i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : t.altitude i₁ = t.mongePlane i₂ i₃
参数：t : Triangle Real P；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.mongePlane_def`：mongePlane_def {n : Nat} (s : Simplex Rea
l P (n + 2)) (i₁ i₂ : Fin (n + 3)) : s.mongePlane i₁ i₂ = mk' (({i₁, i₂}ᶜ : Fins
et (Fin (n + 3))).c…
· 使用定理 `Affine.Simplex.altitude_def`：altitude_def {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.altitude i = mk' (s.points i) (affineSpan Real (s.point
s '' {i}ᶜ)).direc…
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Finset.centroid_singleton`：centroid_singleton (p : ι -> P) (i : ι) : ({i
} : Finset ι).centroid k p = p i
· 使用定理 `vectorSpan_image_eq_span_vsub_set_left_ne`：vectorSpan_image_eq_span_vsub
_set_left_ne (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s) : vectorSpan k (p ''
 s) = Submodule.span k ((p i -ᵥ…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}

--- 原说明 ---
In the case of a triangle, altitudes are the same thing as Monge
planes.
-/
theorem altitude_eq_mongePlane (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) : t.altitude i₁ = t.mongePlane i₂ i₃ := by
  have hs : ({i₂, i₃}ᶜ : Finset (Fin 3)) = {i₁} := by decide +revert
  have he : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by grind
  rw [mongePlane_def, altitude_def, direction_affineSpan, hs, he, centroid_singleton,
    vectorSpan_image_eq_span_vsub_set_left_ne ℝ _ (Set.mem_insert i₂ _)]
  simp [h₂₃]

/-- The orthocenter lies in the altitudes. -/
/-
**Affine.Triangle.orthocenter_mem_altitude** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Tri
angle`。
形式化陈述：orthocenter_mem_altitude (t : Triangle Real P) {i₁ : Fin 3} : t.orthocente
r in t.altitude i₁
参数：t : Triangle Real P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `Affine.Triangle.altitude_eq_mongePlane`：altitude_eq_mongePlane (t : Tria
ngle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i
₃) : t.altitude i₁ = t.monge…
· 使用定理 `Affine.Simplex.mongePoint_mem_mongePlane`：mongePoint_mem_mongePlane {n :
 Nat} (s : Simplex Real P (n + 2)) {i₁ i₂ : Fin (n + 3)} : s.mongePoint in s.mon
gePlane i₁ i₂

--- 原说明 ---
The orthocenter lies in the altitudes.
-/
theorem orthocenter_mem_altitude (t : Triangle ℝ P) {i₁ : Fin 3} :
    t.orthocenter ∈ t.altitude i₁ := by
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : ∃ i₂ i₃, i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃ := by
    decide +revert
  rw [orthocenter_eq_mongePoint, t.altitude_eq_mongePlane h₁₂ h₁₃ h₂₃]
  exact t.mongePoint_mem_mongePlane

/-- The orthocenter is the only point lying in any two of the
altitudes. -/
/-
**Affine.Triangle.eq_orthocenter_of_forall_mem_altitude** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Triangle`。
形式化陈述：eq_orthocenter_of_forall_mem_altitude {t : Triangle Real P} {i₁ i₂ : Fin 3
} {p : P} (h₁₂ : i₁ != i₂) (h₁ : p in t.altitude i₁) (h₂ : p in t.altitude i₂) :
 p = t.orthocenter
参数：h₁₂ : i₁ != i₂；h₁ : p in t.altitude i₁；h₂ : p in t.altitude i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `Affine.Triangle.altitude_eq_mongePlane`：altitude_eq_mongePlane (t : Tria
ngle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i
₃) : t.altitude i₁ = t.monge…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Affine.Simplex.eq_mongePoint_of_forall_mem_mongePlane`：eq_mongePoint_of_
forall_mem_mongePlane {n : Nat} {s : Simplex Real P (n + 2)} {i₁ : Fin (n + 3)} 
{p : P} (h : forall i₂, i₁ != i₂ -> p in s.…

--- 原说明 ---
The orthocenter is the only point lying in any two of the
altitudes.
-/
theorem eq_orthocenter_of_forall_mem_altitude {t : Triangle ℝ P} {i₁ i₂ : Fin 3} {p : P}
    (h₁₂ : i₁ ≠ i₂) (h₁ : p ∈ t.altitude i₁) (h₂ : p ∈ t.altitude i₂) : p = t.orthocenter := by
  obtain ⟨i₃, h₂₃, h₁₃⟩ : ∃ i₃, i₂ ≠ i₃ ∧ i₁ ≠ i₃ := by
    clear h₁ h₂
    decide +revert
  rw [t.altitude_eq_mongePlane h₁₃ h₁₂ h₂₃.symm] at h₁
  rw [t.altitude_eq_mongePlane h₂₃ h₁₂.symm h₁₃.symm] at h₂
  rw [orthocenter_eq_mongePoint]
  have ha : ∀ i, i₃ ≠ i → p ∈ t.mongePlane i₃ i := by
    intro i hi
    obtain rfl | rfl : i₁ = i ∨ i₂ = i := by lia
    all_goals assumption
  exact eq_mongePoint_of_forall_mem_mongePlane ha

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
/-
**Affine.Triangle.dist_orthocenter_reflection_circumcenter** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Triangle`。
形式化陈述：dist_orthocenter_reflection_circumcenter (t : Triangle Real P) {i₁ i₂ : Fi
n 3} (h : i₁ != i₂) : dist t.orthocenter (reflection (affineSpan Real (t.points 
'' {i₁, i₂})) t.circumcenter) = t.circumradius
参数：t : Triangle Real P；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Affine.Simplex.circumradius_nonneg`：circumradius_nonneg {n : Nat} (s : S
implex Real P n) : 0 <= s.circumradius
· 使用定理 `Affine.Simplex.reflection_circumcenter_eq_affineCombination_of_pointsWit
hCircumcenter`：reflection_circumcenter_eq_affineCombination_of_pointsWithCircumc
enter {n : Nat} (s : Simplex Real P n) {i₁ i₂ : Fin (n + 1)} (h : i₁ != i₂)…
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `Affine.Simplex.mongePoint_eq_affineCombination_of_pointsWithCircumcenter
`：mongePoint_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simpl
ex Real P (n + 2)) : s.mongePoint = (univ : Finset (PointsWith…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.dist_affineCombination`：dist_affineCombination {ι : Ty
pe*} {s : Finset ι} {w₁ w₂ : ι -> Real} (p : ι -> P) (h₁ : ∑ i in s, w₁ i = 1) (
h₂ : ∑ i in s, w₂ i = 1) : by …
· 使用定理 `Affine.Simplex.sum_mongePointWeightsWithCircumcenter`：sum_mongePointWeig
htsWithCircumcenter (n : Nat) : ∑ i, mongePointWeightsWithCircumcenter n i = 1
· 使用定理 `Affine.Simplex.sum_reflectionCircumcenterWeightsWithCircumcenter`：sum_re
flectionCircumcenterWeightsWithCircumcenter {n : Nat} {i₁ i₂ : Fin (n + 1)} (h :
 i₁ != i₂) : ∑ i, reflectionCircumcenterWeightsWithCir…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius.
-/
theorem dist_orthocenter_reflection_circumcenter (t : Triangle ℝ P) {i₁ i₂ : Fin 3} (h : i₁ ≠ i₂) :
    dist t.orthocenter (reflection (affineSpan ℝ (t.points '' {i₁, i₂})) t.circumcenter) =
      t.circumradius := by
  rw [← mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg,
    t.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter h,
    t.orthocenter_eq_mongePoint, mongePoint_eq_affineCombination_of_pointsWithCircumcenter,
    dist_affineCombination t.pointsWithCircumcenter (sum_mongePointWeightsWithCircumcenter _)
      (sum_reflectionCircumcenterWeightsWithCircumcenter h)]
  simp_rw [sum_pointsWithCircumcenter, Pi.sub_apply, mongePointWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter]
  have hu : ({i₁, i₂} : Finset (Fin 3)) ⊆ univ := subset_univ _
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
      ∃ i₃, univ \ ({i₁, i₂} : Finset (Fin 3)) = {i₃} ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂ := by
    decide +revert
  simp_rw [← sum_sdiff hu, hi₃]
  norm_num [hi₃₁, hi₃₂]

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`Finset`. -/
/-
**Affine.Triangle.dist_orthocenter_reflection_circumcenter_finset** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Triangle`。
形式化陈述：dist_orthocenter_reflection_circumcenter_finset (t : Triangle Real P) {i₁ 
i₂ : Fin 3} (h : i₁ != i₂) : dist t.orthocenter (reflection (affineSpan Real (t.
points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.circumcenter) = t.circumradius
参数：t : Triangle Real P；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Finset.instNonemptyElemCoeInsert`：∀ {α : Type u_1} [inst : DecidableEq α
] (i : α) (s : Finset α), Nonempty ↑↑(insert i s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.reflection.congr_simp`：∀ {𝕜 : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2 : In
nerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Triangle.dist_orthocenter_reflection_circumcenter`：dist_orthocent
er_reflection_circumcenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) 
: dist t.orthocenter (reflection (affineSpan R…

--- 原说明 ---
The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`Finset`.
-/
theorem dist_orthocenter_reflection_circumcenter_finset (t : Triangle ℝ P) {i₁ i₂ : Fin 3}
    (h : i₁ ≠ i₂) :
    dist t.orthocenter
        (reflection (affineSpan ℝ (t.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.circumcenter) =
      t.circumradius := by
  simp only [coe_insert, coe_singleton]
  exact dist_orthocenter_reflection_circumcenter _ h

/-- The distance from the circumcenter to the reflection of the orthocenter in a side equals the
circumradius. -/
/-
**Affine.Triangle.dist_circumcenter_reflection_orthocenter** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Triangle`。
形式化陈述：dist_circumcenter_reflection_orthocenter (t : Triangle Real P) {i₁ i₂ : Fi
n 3} (h : i₁ != i₂) : dist t.circumcenter (reflection (affineSpan Real (t.points
 '' {i₁, i₂})) t.orthocenter) = t.circumradius
参数：t : Triangle Real P；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.dist_reflection`：dist_reflection (s : AffineSubspace 𝕜
 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p₁ p₂ : P) : dist p₁ (re
flection s p₂) = dist (…
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Affine.Triangle.dist_orthocenter_reflection_circumcenter`：dist_orthocent
er_reflection_circumcenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) 
: dist t.orthocenter (reflection (affineSpan R…

--- 原说明 ---
The distance from the circumcenter to the reflection of the orthocenter in a sid
e equals the
circumradius.
-/
theorem dist_circumcenter_reflection_orthocenter (t : Triangle ℝ P) {i₁ i₂ : Fin 3} (h : i₁ ≠ i₂) :
    dist t.circumcenter (reflection (affineSpan ℝ (t.points '' {i₁, i₂})) t.orthocenter) =
      t.circumradius := by
  rw [EuclideanGeometry.dist_reflection, dist_comm, dist_orthocenter_reflection_circumcenter t h]

/-- The distance from the circumcenter to the reflection of the orthocenter in a side equals the
circumradius, variant using a `Finset`. -/
/-
**Affine.Triangle.dist_circumcenter_reflection_orthocenter_finset** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Triangle`。
形式化陈述：dist_circumcenter_reflection_orthocenter_finset (t : Triangle Real P) {i₁ 
i₂ : Fin 3} (h : i₁ != i₂) : dist t.circumcenter (reflection (affineSpan Real (t
.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.orthocenter) = t.circumradius
参数：t : Triangle Real P；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Finset.instNonemptyElemCoeInsert`：∀ {α : Type u_1} [inst : DecidableEq α
] (i : α) (s : Finset α), Nonempty ↑↑(insert i s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.reflection.congr_simp`：∀ {𝕜 : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2 : In
nerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Triangle.dist_circumcenter_reflection_orthocenter`：dist_circumcen
ter_reflection_orthocenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) 
: dist t.circumcenter (reflection (affineSpan …

--- 原说明 ---
The distance from the circumcenter to the reflection of the orthocenter in a sid
e equals the
circumradius, variant using a `Finset`.
-/
theorem dist_circumcenter_reflection_orthocenter_finset (t : Triangle ℝ P) {i₁ i₂ : Fin 3}
    (h : i₁ ≠ i₂) :
    dist t.circumcenter
      (reflection (affineSpan ℝ (t.points '' ↑({i₁, i₂} : Finset (Fin 3)))) t.orthocenter) =
      t.circumradius := by
  simp only [coe_insert, coe_singleton]
  exact dist_circumcenter_reflection_orthocenter _ h

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
/-
**Affine.Triangle.affineSpan_orthocenter_point_le_altitude** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Triangle`。
形式化陈述：affineSpan_orthocenter_point_le_altitude (t : Triangle Real P) (i : Fin 3)
 : line[Real, t.orthocenter, t.points i] <= t.altitude i
参数：t : Triangle Real P；i : Fin 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Affine.Triangle.orthocenter_mem_altitude`：orthocenter_mem_altitude (t : 
Triangle Real P) {i₁ : Fin 3} : t.orthocenter in t.altitude i₁
· 使用定理 `Affine.Simplex.mem_altitude`：mem_altitude {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.points i in s.altitude i

--- 原说明 ---
The affine span of the orthocenter and a vertex is contained in
the altitude.
-/
theorem affineSpan_orthocenter_point_le_altitude (t : Triangle ℝ P) (i : Fin 3) :
    line[ℝ, t.orthocenter, t.points i] ≤ t.altitude i := by
  refine affineSpan_le_of_subset_coe ?_
  rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
/-
**Affine.Triangle.altitude_replace_orthocenter_eq_affineSpan** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Triangle`。
形式化陈述：altitude_replace_orthocenter_eq_affineSpan {t₁ t₂ : Triangle Real P} {i₁ i
₂ i₃ j₁ j₂ j₃ : Fin 3} (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ : i₂ != i₃) (hj
₁₂ : j₁ != j₂) (hj₁₃ : j₁ != j₃) (hj₂₃ : j₂ != j₃) (h₁ : t₂.points j₁ = t₁.ortho
center) (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) : 
t₂.altitude j₂ = line[Real, t₁.points i₁, t₁.points i₂]
参数：hi₁₂ : i₁ != i₂；hi₁₃ : i₁ != i₃；hi₂₃ : i₂ != i₃；hj₁₂ : j₁ != j₂；hj₁₃ : j₁ != 
j₃；hj₂₃ : j₂ != j₃；h₁ : t₂.points j₁ = t₁.orthocenter；h₂ : t₂.points j₂ = t₁.poi
nts i₂；h₃ : t₂.points j₃ = t₁.points i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.affineSpan_pair_eq_altitude_iff`：affineSpan_pair_eq_altit
ude_iff {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) (p : P) : 
line[Real, p, s.points i] = s.altitu…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Affine.Triangle.orthocenter_mem_affineSpan`：orthocenter_mem_affineSpan (
t : Triangle Real P) : t.orthocenter in affineSpan Real (Set.range t.points)
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `Affine.Triangle.affineSpan_orthocenter_point_le_altitude`：affineSpan_ort
hocenter_point_le_altitude (t : Triangle Real P) (i : Fin 3) : line[Real, t.orth
ocenter, t.points i] <= t.altitude i
· 使用定理 `Affine.Simplex.vectorSpan_isOrtho_altitude_direction`：vectorSpan_isOrtho
_altitude_direction {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : vectorS
pan Real (s.points '' {i}ᶜ) ⟂ (s.altitude …
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`.
-/
theorem altitude_replace_orthocenter_eq_affineSpan {t₁ t₂ : Triangle ℝ P}
    {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3} (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂)
    (hj₁₃ : j₁ ≠ j₃) (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter)
    (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) :
    t₂.altitude j₂ = line[ℝ, t₁.points i₁, t₁.points i₂] := by
  symm
  rw [← h₂, t₂.affineSpan_pair_eq_altitude_iff]
  rw [h₂]
  use t₁.independent.injective.ne hi₁₂
  have he : affineSpan ℝ (Set.range t₂.points) = affineSpan ℝ (Set.range t₁.points) := by
    refine ext_of_direction_eq ?_
      ⟨t₁.points i₃, mem_affineSpan ℝ ⟨j₃, h₃⟩, mem_affineSpan ℝ (Set.mem_range_self _)⟩
    refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_le_of_subset_coe ?_))
      ?_
    · have hu : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by grind
      rw [← Set.image_univ, hu, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, h₁,
        h₂, h₃, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact
        ⟨t₁.orthocenter_mem_affineSpan, mem_affineSpan ℝ (Set.mem_range_self _),
          mem_affineSpan ℝ (Set.mem_range_self _)⟩
    · rw [direction_affineSpan, direction_affineSpan,
        t₁.independent.finrank_vectorSpan (Fintype.card_fin _),
        t₂.independent.finrank_vectorSpan (Fintype.card_fin _)]
  rw [he]
  use mem_affineSpan ℝ (Set.mem_range_self _)
  have hu : ({j₂}ᶜ : Set _) = {j₁, j₃} := by grind
  rw [hu, Set.image_insert_eq, Set.image_singleton, h₁, h₃]
  have hle : (t₁.altitude i₃).directionᗮ ≤ line[ℝ, t₁.orthocenter, t₁.points i₃].directionᗮ :=
    Submodule.orthogonal_le (direction_le (affineSpan_orthocenter_point_le_altitude _ _))
  refine hle ((t₁.vectorSpan_isOrtho_altitude_direction i₃) ?_)
  have hui : ({i₃}ᶜ : Set _) = {i₁, i₂} := by grind
  rw [hui, Set.image_insert_eq, Set.image_singleton]
  exact vsub_mem_vectorSpan ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
/-
**Affine.Triangle.orthocenter_replace_orthocenter_eq_point** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Triangle`。
形式化陈述：orthocenter_replace_orthocenter_eq_point {t₁ t₂ : Triangle Real P} {i₁ i₂ 
i₃ j₁ j₂ j₃ : Fin 3} (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ : i₂ != i₃) (hj₁₂
 : j₁ != j₂) (hj₁₃ : j₁ != j₃) (hj₂₃ : j₂ != j₃) (h₁ : t₂.points j₁ = t₁.orthoce
nter) (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) : t₂
.orthocenter = t₁.points i₁
参数：hi₁₂ : i₁ != i₂；hi₁₃ : i₁ != i₃；hi₂₃ : i₂ != i₃；hj₁₂ : j₁ != j₂；hj₁₃ : j₁ != 
j₃；hj₂₃ : j₂ != j₃；h₁ : t₂.points j₁ = t₁.orthocenter；h₂ : t₂.points j₂ = t₁.poi
nts i₂；h₃ : t₂.points j₃ = t₁.points i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Triangle.eq_orthocenter_of_forall_mem_altitude`：eq_orthocenter_of
_forall_mem_altitude {t : Triangle Real P} {i₁ i₂ : Fin 3} {p : P} (h₁₂ : i₁ != 
i₂) (h₁ : p in t.altitude i₁) (h₂ : p in t.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.altitude_replace_orthocenter_eq_affineSpan`：altitude_rep
lace_orthocenter_eq_affineSpan {t₁ t₂ : Triangle Real P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fi
n 3} (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ :…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced.
-/
theorem orthocenter_replace_orthocenter_eq_point {t₁ t₂ : Triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) : t₂.orthocenter = t₁.points i₁ := by
  refine (Triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ ?_ ?_).symm
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
    exact mem_affineSpan ℝ (Set.mem_insert _ _)
  · rw [altitude_replace_orthocenter_eq_affineSpan hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂]
    exact mem_affineSpan ℝ (Set.mem_insert _ _)

end Triangle

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter. -/
/-
**EuclideanGeometry.OrthocentricSystem** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeome
try`。
形式化陈述：OrthocentricSystem (s : Set P) : Prop
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter.
-/
def OrthocentricSystem (s : Set P) : Prop :=
  ∃ t : Triangle ℝ P,
    t.orthocenter ∉ Set.range t.points ∧ s = insert t.orthocenter (Set.range t.points)

/-- This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`. -/
/-
**EuclideanGeometry.exists_of_range_subset_orthocentricSystem** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_of_range_subset_orthocentricSystem {t : Triangle Real P} (ho : t.or
thocenter ∉ Set.range t.points) {p : Fin 3 -> P} (hps : Set.range p subseteq ins
ert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) : (exists i
₁ i₂ i₃ j₂ j₃ : Fin 3, i₁ != i₂ ∧ i₁ != i₃ ∧ i₂ != i₃ ∧ (forall i : Fin 3, i = i
₁ ∨ i = i₂ ∨ i = i₃) ∧ p i₁ = t.orthocenter ∧ j₂ != j₃ ∧ t.points j₂ = p i₂ ∧ t.
points j₃ = p i₃) ∨ Set.range p = Set.range t.points
参数：ho : t.orthocenter ∉ Set.range t.points；hps : Set.range p subseteq insert t.o
rthocenter (Set.range t.points)；hpi : Function.Injective p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Set.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne : b in insert a s -
> b != a -> b in s
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Set.eq_of_subset_of_card_le`：eq_of_subset_of_card_le {s t : Set α} [Fint
ype s] [Fintype t] (hsub : s subseteq t) (hcard : Fintype.card t <= Fintype.card
 s) : s = t
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `Set.card_range_of_injective`：card_range_of_injective [Fintype α] {f : α 
-> β} (hf : Injective f) [Fintype (range f)] : Fintype.card (range f) = Fintype.
card α
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`.
-/
theorem exists_of_range_subset_orthocentricSystem {t : Triangle ℝ P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 → P}
    (hps : Set.range p ⊆ insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    (∃ i₁ i₂ i₃ j₂ j₃ : Fin 3,
      i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ (∀ i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃) ∧
        p i₁ = t.orthocenter ∧ j₂ ≠ j₃ ∧ t.points j₂ = p i₂ ∧ t.points j₃ = p i₃) ∨
      Set.range p = Set.range t.points := by
  by_cases h : t.orthocenter ∈ Set.range p
  · left
    rcases h with ⟨i₁, h₁⟩
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
        ∃ i₂ i₃ : Fin 3, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ ∀ i : Fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃ := by
      clear h₁
      decide +revert
    have h : ∀ i, i₁ ≠ i → ∃ j : Fin 3, t.points j = p i := by
      intro i hi
      replace hps := Set.mem_of_mem_insert_of_ne
        (Set.mem_of_mem_of_subset (Set.mem_range_self i) hps) (h₁ ▸ hpi.ne hi.symm)
      exact hps
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩
    have hj₂₃ : j₂ ≠ j₃ := by
      intro he
      rw [he, h₃] at h₂
      exact h₂₃.symm (hpi h₂)
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩
  · right
    have hs := Set.subset_sdiff_singleton hps h
    rw [Set.insert_sdiff_self_of_notMem ho] at hs
    classical
    refine Set.eq_of_subset_of_card_le hs ?_
    rw [Set.card_range_of_injective hpi, Set.card_range_of_injective t.independent.injective]

/-- For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the circumradius. -/
/-
**EuclideanGeometry.exists_dist_eq_circumradius_of_subset_insert_orthocenter** 是
 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle Rea
l P} (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 -> P} (hps : Set.range
 p subseteq insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective
 p) : exists c in affineSpan Real (Set.range t.points), forall p₁ in Set.range p
, dist p₁ c = t.circumradius
参数：ho : t.orthocenter ∉ Set.range t.points；hps : Set.range p subseteq insert t.o
rthocenter (Set.range t.points)；hpi : Function.Injective p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_of_range_subset_orthocentricSystem`：exists_of_r
ange_subset_orthocentricSystem {t : Triangle Real P} (ho : t.orthocenter ∉ Set.r
ange t.points) {p : Fin 3 -> P} (hps : Set.range …
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `EuclideanGeometry.reflection_mem_of_le_of_mem`：reflection_mem_of_le_of_m
em {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁] [s₁.direction.HasOrthogonalProject
ion] (hle : s₁ <= s₂) {p : P} (hp :…
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Triangle.dist_orthocenter_reflection_circumcenter`：dist_orthocent
er_reflection_circumcenter (t : Triangle Real P) {i₁ i₂ : Fin 3} (h : i₁ != i₂) 
: dist t.orthocenter (reflection (affineSpan R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.dist_reflection_eq_of_mem`：dist_reflection_eq_of_mem (
s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ :
 P} (hp₁ : p₁ in s) (p₂ : P) : di…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the circumradius.
-/
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle ℝ P}
    (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 → P}
    (hps : Set.range p ⊆ insert t.orthocenter (Set.range t.points)) (hpi : Function.Injective p) :
    ∃ c ∈ affineSpan ℝ (Set.range t.points), ∀ p₁ ∈ Set.range p, dist p₁ c = t.circumradius := by
  rcases exists_of_range_subset_orthocentricSystem ho hps hpi with
    (⟨i₁, i₂, i₃, j₂, j₃, _, _, _, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · use reflection (affineSpan ℝ (t.points '' {j₂, j₃})) t.circumcenter,
      reflection_mem_of_le_of_mem (affineSpan_mono ℝ (Set.image_subset_range _ _))
        t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rcases hp₁ with ⟨i, rfl⟩
    have h₁₂₃ := h₁₂₃ i
    repeat' rcases h₁₂₃ with h₁₂₃ | h₁₂₃
    · convert! Triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
    · rw [← h₂, dist_reflection_eq_of_mem _
       (mem_affineSpan ℝ (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
      exact t.dist_circumcenter_eq_circumradius _
    · rw [← h₃,
        dist_reflection_eq_of_mem _
          (mem_affineSpan ℝ
            (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
      exact t.dist_circumcenter_eq_circumradius _
  · use t.circumcenter, t.circumcenter_mem_affineSpan
    intro p₁ hp₁
    rw [hs] at hp₁
    rcases hp₁ with ⟨i, rfl⟩
    exact t.dist_circumcenter_eq_circumradius _

/-- Any three points in an orthocentric system are affinely independent. -/
/-
**EuclideanGeometry.OrthocentricSystem.affineIndependent** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry.OrthocentricSystem`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : Set P},   EuclideanGeometry.OrthocentricSystem s →     ∀ {p : Fin 3 → P}, Se
t.range p ⊆ s → Function.Injective p → AffineIndependent ℝ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_dist_eq_circumradius_of_subset_insert_orthocent
er`：exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle Real 
P} (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 -> P} (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Cospherical.affineIndependent`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
Any three points in an orthocentric system are affinely independent.
-/
theorem OrthocentricSystem.affineIndependent {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p := by
  rcases ho with ⟨t, hto, hst⟩
  rw [hst] at hps
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, _, hc⟩
  exact Cospherical.affineIndependent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi

/-- Any three points in an orthocentric system span the same subspace
as the whole orthocentric system. -/
/-
**EuclideanGeometry.affineSpan_of_orthocentricSystem** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：affineSpan_of_orthocentricSystem {s : Set P} (ho : OrthocentricSystem s) {
p : Fin 3 -> P} (hps : Set.range p subseteq s) (hpi : Function.Injective p) : af
fineSpan Real (Set.range p) = affineSpan Real s
参数：ho : OrthocentricSystem s；hps : Set.range p subseteq s；hpi : Function.Injecti
ve p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.OrthocentricSystem.affineIndependent`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSpan_insert_eq_affineSpan`：affineSpan_insert_eq_affineSpan {p : P}
 {ps : Set P} (h : p in affineSpan k ps) : affineSpan k (insert p ps) = affineSp
an k ps
· 使用定理 `Affine.Triangle.orthocenter_mem_affineSpan`：orthocenter_mem_affineSpan (
t : Triangle Real P) : t.orthocenter in affineSpan Real (Set.range t.points)
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
Any three points in an orthocentric system span the same subspace
as the whole orthocentric system.
-/
theorem affineSpan_of_orthocentricSystem {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) :
    affineSpan ℝ (Set.range p) = affineSpan ℝ s := by
  have ha := ho.affineIndependent hps hpi
  rcases ho with ⟨t, _, hts⟩
  have hs : affineSpan ℝ s = affineSpan ℝ (Set.range t.points) := by
    rw [hts, affineSpan_insert_eq_affineSpan ℝ t.orthocenter_mem_affineSpan]
  refine ext_of_direction_eq ?_
    ⟨p 0, mem_affineSpan ℝ (Set.mem_range_self _), mem_affineSpan ℝ (hps (Set.mem_range_self _))⟩
  have hfd : FiniteDimensional ℝ (affineSpan ℝ s).direction := by rw [hs]; infer_instance
  refine Submodule.eq_of_le_of_finrank_eq (direction_le (affineSpan_mono ℝ hps)) ?_
  rw [hs, direction_affineSpan, direction_affineSpan, ha.finrank_vectorSpan (Fintype.card_fin _),
    t.independent.finrank_vectorSpan (Fintype.card_fin _)]

/-- All triangles in an orthocentric system have the same circumradius. -/
/-
**EuclideanGeometry.OrthocentricSystem.exists_circumradius_eq** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry.OrthocentricSystem`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : Set P},   EuclideanGeometry.OrthocentricSystem s →     ∃ r, ∀ (t : Affine.Tr
iangle ℝ P), Set.range t.points ⊆ s → Affine.Simplex.circumradius t = r
参数：t : Affine.Triangle ℝ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_dist_eq_circumradius_of_subset_insert_orthocent
er`：exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : Triangle Real 
P} (ho : t.orthocenter ∉ Set.range t.points) {p : Fin 3 -> P} (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.eq_circumradius_of_dist_eq`：eq_circumradius_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `EuclideanGeometry.affineSpan_of_orthocentricSystem`：affineSpan_of_orthoc
entricSystem {s : Set P} (ho : OrthocentricSystem s) {p : Fin 3 -> P} (hps : Set
.range p subseteq s) (hpi : Function.Inj…
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
All triangles in an orthocentric system have the same circumradius.
-/
theorem OrthocentricSystem.exists_circumradius_eq {s : Set P} (ho : OrthocentricSystem s) :
    ∃ r : ℝ, ∀ t : Triangle ℝ P, Set.range t.points ⊆ s → t.circumradius = r := by
  rcases ho with ⟨t, hto, hts⟩
  use t.circumradius
  intro t₂ ht₂
  have ht₂s := ht₂
  rw [hts] at ht₂
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
      t₂.independent.injective with
    ⟨c, hc, h⟩
  rw [Set.forall_mem_range] at h
  have hs : Set.range t.points ⊆ s := by
    rw [hts]
    exact Set.subset_insert _ _
  rw [affineSpan_of_orthocentricSystem ⟨t, hto, hts⟩ hs t.independent.injective,
    ← affineSpan_of_orthocentricSystem ⟨t, hto, hts⟩ ht₂s t₂.independent.injective] at hc
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm

/-- Given any triangle in an orthocentric system, the fourth point is
its orthocenter. -/
/-
**EuclideanGeometry.OrthocentricSystem.eq_insert_orthocenter** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.OrthocentricSystem`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : Set P},   EuclideanGeometry.OrthocentricSystem s →     ∀ {t : Affine.Triangl
e ℝ P}, Set.range t.points ⊆ s → s = insert t.orthocenter (Set.range t.points)
参数：Set.range t.points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_of_range_subset_orthocentricSystem`：exists_of_r
ange_subset_orthocentricSystem {t : Triangle Real P} (ho : t.orthocenter ∉ Set.r
ange t.points) {p : Fin 3 -> P} (hps : Set.range …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Triangle.orthocenter_replace_orthocenter_eq_point`：orthocenter_re
place_orthocenter_eq_point {t₁ t₂ : Triangle Real P} {i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3}
 (hi₁₂ : i₁ != i₂) (hi₁₃ : i₁ != i₃) (hi₂₃ : i…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Affine.Triangle.orthocenter_eq_of_range_eq`：orthocenter_eq_of_range_eq {
t₁ t₂ : Triangle Real P} (h : Set.range t₁.points = Set.range t₂.points) : t₁.or
thocenter = t₂.orthocenter

--- 原说明 ---
Given any triangle in an orthocentric system, the fourth point is
its orthocenter.
-/
theorem OrthocentricSystem.eq_insert_orthocenter {s : Set P} (ho : OrthocentricSystem s)
    {t : Triangle ℝ P} (ht : Set.range t.points ⊆ s) :
    s = insert t.orthocenter (Set.range t.points) := by
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩
  rw [ht₀s] at ht
  rcases exists_of_range_subset_orthocentricSystem ht₀o ht t.independent.injective with
    (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
  · obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
        ∃ j₁ : Fin 3, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ ∀ j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := by
      clear h₂ h₃
      decide +revert
    suffices h : t₀.points j₁ = t.orthocenter by
      have hui : (Set.univ : Set (Fin 3)) = {i₁, i₂, i₃} := by ext x; simpa using h₁₂₃ x
      have huj : (Set.univ : Set (Fin 3)) = {j₁, j₂, j₃} := by ext x; simpa using hj₁₂₃ x
      rw [← h, ht₀s, ← Set.image_univ, huj, ← Set.image_univ, hui]
      simp_rw [Set.image_insert_eq, Set.image_singleton, h₁, ← h₂, ← h₃]
      rw [Set.insert_comm]
    exact
      (Triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm
          h₃.symm).symm
  · rw [hs]
    convert! ht₀s using 2
    exact Triangle.orthocenter_eq_of_range_eq hs

end EuclideanGeometry

