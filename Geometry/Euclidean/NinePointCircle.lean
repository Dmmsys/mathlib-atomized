/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Nine-point circle

This file defines the nine-point circle of a triangle, and its higher dimension analogue, the
3(n+1)-point sphere of a simplex. Specifically for triangles, we show that it passes through nine
specific points as desired.

## Main definitions
* `Affine.Simplex.ninePointCircle`: the 3(n+1)-point sphere of a simplex.
* `Affine.Simplex.eulerPoint`: the $1/n$th of the way from the Monge point to a vertex.
* `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`: the 3(n+1)-point sphere passes through
  the centroid of each face of the simplex
* `Affine.Simplex.eulerPoint_mem_ninePointCircle`: the 3(n+1)-point sphere passes through all Euler
  points.
* `Affine.Triangle.altitudeFoot_mem_ninePointCircle`: the nine-point circle passes through all
  three altitude feet of the triangle.

## References
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)
-/

@[expose] public section

noncomputable section

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

/--
The 3(n+1)-point sphere of a simplex. Due to the lack of a better name and to avoid numbers in the
identifier, we still use the name "nine-point circle" even for higher dimensions. The center
$N$ is defined on the Euler line, collinear with circumcenter $O$ and centroid $G$, in the order of
$O$, $G$, and $N$, with $OG : GN = n : 1$. The radius is $1/n$ of the circumradius.
-/
/-
**Affine.Simplex.ninePointCircle** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：ninePointCircle {n : Nat} (s : Simplex Real P n) : Sphere P where center
参数：s : Simplex Real P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 3(n+1)-point sphere of a simplex. Due to the lack of a better name and to av
oid numbers in the
identifier, we still use the name "nine-point circle" even for higher dimensions
. The center
$N$ is defined on the Euler line, collinear with circumcenter $O$ and centroid $
G$, in the order of
$O$, $G$, and $N$, with $OG : GN = n : 1$. The radius is $1/n$ of the circumradi
us.
-/
def ninePointCircle {n : ℕ} (s : Simplex ℝ P n) : Sphere P where
  center := ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : ℝ)
/-
**Affine.Simplex.ninePointCircle_center** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：ninePointCircle_center {n : Nat} (s : Simplex Real P n) : s.ninePointCircl
e.center = ((n + 1) / n : Real) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcent
er
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ninePointCircle_center {n : ℕ} (s : Simplex ℝ P n) : s.ninePointCircle.center =
    ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter := rfl
/-
**Affine.Simplex.ninePointCircle_center_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：ninePointCircle_center_mem_affineSpan {n : Nat} (s : Simplex Real P n) : s
.ninePointCircle.center in affineSpan Real (Set.range s.points)
参数：s : Simplex Real P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ninePointCircle_center`：ninePointCircle_center {n : Nat} 
(s : Simplex Real P n) : s.ninePointCircle.center = ((n + 1) / n : Real) • (s.ce
ntroid -ᵥ s.circumcenter) +…
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Affine.Simplex.centroid_mem_affineSpan`：centroid_mem_affineSpan [CharZer
o k] {n : Nat} (s : Simplex k P n) : s.centroid in affineSpan k (Set.range s.poi
nts)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
-/
theorem ninePointCircle_center_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.ninePointCircle.center ∈ affineSpan ℝ (Set.range s.points) := by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan
/-
**Affine.Simplex.ninePointCircle_radius** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：ninePointCircle_radius {n : Nat} (s : Simplex Real P n) : s.ninePointCircl
e.radius = s.circumradius / (n : Real)
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ninePointCircle_radius {n : ℕ} (s : Simplex ℝ P n) :
    s.ninePointCircle.radius = s.circumradius / (n : ℝ) := rfl

@[simp]
/-
**Affine.Simplex.ninePointCircle_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：ninePointCircle_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1
) ≃ Fin (m + 1)) : (s.reindex e).ninePointCircle = s.ninePointCircle
参数：s : Simplex Real P n；e : Fin (n + 1) ≃ Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_reindex`：centroid_reindex {m n : Nat} (s : Simpl
ex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).centroid = s.centroid
· 使用定理 `Affine.Simplex.circumcenter_reindex`：circumcenter_reindex {m n : Nat} (s
 : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).circumcente
r = s.circumcenter
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.circumradius_reindex`：circumradius_reindex {m n : Nat} (s
 : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).circumradiu
s = s.circumradius
-/
theorem ninePointCircle_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).ninePointCircle = s.ninePointCircle := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]
/-
**Affine.Simplex.ninePointCircle_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：ninePointCircle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductS
pace Real V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : Nat} (s : Simplex Re
al P n) (f : P ->ᵃⁱ[Real] P₂) : (s.map f.toAffineMap f.injective).ninePointCircl
e = { center
参数：s : Simplex Real P n；f : P ->ᵃⁱ[Real] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Affine.Simplex.circumradius_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
-/
theorem ninePointCircle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).ninePointCircle =
    { center := f s.ninePointCircle.center, radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]
/-
**Affine.Simplex.ninePointCircle_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：ninePointCircle_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubsp
ace Real P) (hS : affineSpan Real (Set.range s.points) <= S) : haveI
参数：s : Simplex Real P n；S : AffineSubspace Real P；hS : affineSpan Real (Set.rang
e s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Affine.Simplex.ninePointCircle_center_mem_affineSpan`：ninePointCircle_ce
nter_mem_affineSpan {n : Nat} (s : Simplex Real P n) : s.ninePointCircle.center 
in affineSpan Real (Set.range s.points)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.centroid_restrict`：centroid_restrict [CharZero k] {n : Na
t} (s : Simplex k P n) (S : AffineSubspace k P) (hS : affineSpan k (Set.range s.
points) <= S) : haveI
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Affine.Simplex.circumcenter_restrict`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.circumradius_restrict`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
-/
theorem ninePointCircle_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]
/-
**Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.faceOppositeCentroid i in s.ninePointCircle
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `Affine.Simplex.ninePointCircle_center`：ninePointCircle_center {n : Nat} 
(s : Simplex Real P n) : s.ninePointCircle.center = ((n + 1) / n : Real) • (s.ce
ntroid -ᵥ s.circumcenter) +…
· 使用定理 `Affine.Simplex.ninePointCircle_radius`：ninePointCircle_radius {n : Nat} 
(s : Simplex Real P n) : s.ninePointCircle.radius = s.circumradius / (n : Real)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius'`：dist_circumcenter_eq_
circumradius' {n : Nat} (s : Simplex Real P n) : forall i, dist s.circumcenter (
s.points i) = s.circumradius
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Affine.Simplex.centroid_vsub_point_eq_smul_vsub`：centroid_vsub_point_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.p
oints i = (n : k) • (s.faceOppositeCe…
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
-/
theorem faceOppositeCentroid_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.faceOppositeCentroid i ∈ s.ninePointCircle := by
  rw [mem_sphere, ninePointCircle_center, ninePointCircle_radius,
    ← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [eq_div_iff_mul_eq (by simpa using NeZero.ne n), mul_comm]
  nth_rw 1 [show (n : ℝ) = ‖(n : ℝ)‖ by simp]
  rw [← norm_smul, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul,
    mul_div_cancel₀ _ (by simpa using NeZero.ne n), add_smul, one_smul, ← sub_sub, ← smul_sub,
    vsub_sub_vsub_cancel_right, ← centroid_vsub_point_eq_smul_vsub, vsub_sub_vsub_cancel_left]
/-
**Affine.Simplex.ninePointCircle_eq_circumsphere_medial** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Simplex`。
形式化陈述：ninePointCircle_eq_circumsphere_medial {n : Nat} [NeZero n] (s : Simplex R
eal P n) : s.ninePointCircle = s.medial.circumsphere
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.affineSpan_range_medial`：affineSpan_range_medial [CharZer
o k] (s : Simplex k P n) : affineSpan k (Set.range (s.medial.points)) = affineSp
an k (Set.range (s.points))
· 使用定理 `Affine.Simplex.ninePointCircle_center_mem_affineSpan`：ninePointCircle_ce
nter_mem_affineSpan {n : Nat} (s : Simplex Real P n) : s.ninePointCircle.center 
in affineSpan Real (Set.range s.points)
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`：faceOppositeCen
troid_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (
n + 1)) : s.faceOppositeCentroid i in s.nineP…
-/
theorem ninePointCircle_eq_circumsphere_medial {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    s.ninePointCircle = s.medial.circumsphere := by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

/-- Euler points are a set of points that the `ninePointCircle` passes through. They are defined as
being $1/n$th of the way from the Monge point to a vertex. Specifically for triangles, these are
the midpoints between the orthocenter and a given vertex
(`Affine.Triangle.eulerPoint_eq_midpoint`). -/
/-
**Affine.Simplex.eulerPoint** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：eulerPoint {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
参数：s : Simplex Real P n；i : Fin (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euler points are a set of points that the `ninePointCircle` passes through. They
 are defined as
being $1/n$th of the way from the Monge point to a vertex. Specifically for tria
ngles, these are
the midpoints between the orthocenter and a given vertex
(`Affine.Triangle.eulerPoint_eq_midpoint`).
-/
def eulerPoint {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :=
  (n : ℝ)⁻¹ • (s.points i -ᵥ s.mongePoint) +ᵥ s.mongePoint

@[simp]
/-
**Affine.Simplex.eulerPoint_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：eulerPoint_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ F
in (m + 1)) : (s.reindex e).eulerPoint = s.eulerPoint ∘ e.symm
参数：s : Simplex Real P n；e : Fin (n + 1) ≃ Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.mongePoint_reindex`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eulerPoint_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).eulerPoint = s.eulerPoint ∘ e.symm := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]
/-
**Affine.Simplex.eulerPoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：eulerPoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 
Real V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : Nat} (s : Simplex Real P 
n) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1)) : (s.map f.toAffineMap f.injective).e
ulerPoint i = f (s.eulerPoint i)
参数：s : Simplex Real P n；f : P ->ᵃⁱ[Real] P₂；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `Affine.Simplex.mongePoint_map`：mongePoint_map {V₂ P₂ : Type*} [NormedAdd
CommGroup V₂] [InnerProductSpace Real V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P
₂] {n : Nat} (s : S…
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
theorem eulerPoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).eulerPoint i = f (s.eulerPoint i) := by
  simp [eulerPoint]

@[simp]
/-
**Affine.Simplex.eulerPoint_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：eulerPoint_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace R
eal P) (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) : have
I
参数：s : Simplex Real P n；S : AffineSubspace Real P；hS : affineSpan Real (Set.rang
e s.points) <= S；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.restrict_points_coe`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.mongePoint_restrict`：mongePoint_restrict {n : Nat} (s : S
implex Real P n) (S : AffineSubspace Real P) (hS : affineSpan Real (Set.range s.
points) <= S) : haveI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eulerPoint_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  simp [eulerPoint]
/-
**Affine.Simplex.points_vsub_eulerPoint** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：points_vsub_eulerPoint {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) 
: s.points i -ᵥ s.eulerPoint i = ((n - 1) / n : Real) • (s.points i -ᵥ s.mongePo
int)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.eulerPoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineSubspace.mem_affineSpan_singleton`：mem_affineSpan_singleton : p₁ i
n affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
· 使用定理 `Affine.Simplex.mongePoint_mem_affineSpan`：mongePoint_mem_affineSpan {n :
 Nat} (s : Simplex Real P n) : s.mongePoint in affineSpan Real (Set.range s.poin
ts)
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem points_vsub_eulerPoint {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.eulerPoint i = ((n - 1) / n : ℝ) • (s.points i -ᵥ s.mongePoint) := by
  rw [eulerPoint, vsub_vadd_eq_vsub_sub]
  by_cases hn : n = 0
  · obtain rfl := hn
    have hrange : Set.range s.points = {s.points i} := by simp [Subsingleton.eq_zero (α := Fin 1) i]
    obtain hmonge := s.mongePoint_mem_affineSpan
    rw [hrange, mem_affineSpan_singleton] at hmonge
    simp [hmonge]
  rw [sub_div, div_self (by simpa using hn), one_div, sub_smul, one_smul]
/-
**Affine.Simplex.midpoint_faceOppositeCentroid_eulerPoint** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Simplex`。
形式化陈述：midpoint_faceOppositeCentroid_eulerPoint {n : Nat} [hn : NeZero n] (s : Si
mplex Real P n) (i : Fin (n + 1)) : midpoint Real (s.faceOppositeCentroid i) (s.
eulerPoint i) = s.ninePointCircle.center
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_left_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T
 : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p → p₁ = p₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ninePointCircle_center`：ninePointCircle_center {n : Nat} 
(s : Simplex Real P n) : s.ninePointCircle.center = ((n + 1) / n : Real) • (s.ce
ntroid -ᵥ s.circumcenter) +…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `midpoint_vsub`：midpoint_vsub (p₁ p₂ p : P) : midpoint R p₁ p₂ -ᵥ p = (⅟2
 : R) • (p₁ -ᵥ p) + (⅟2 : R) • (p₂ -ᵥ p)
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Affine.Simplex.eulerPoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter`：mongePoint_eq_
smul_vsub_vadd_circumcenter {n : Nat} (s : Simplex Real P n) : s.mongePoint = ((
(n + 1 : Nat) : Real) / ((n - 1 : Nat) : Real)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.centroid.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module
 k V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_centroid_eq_smul_vsub`：faceOppo
siteCentroid_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fi
n (n + 1)) : s.faceOppositeCentroid i -ᵥ s.centroid …
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_eq_zero_of_right`：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0)
 : a • b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Affine.Simplex.circumcenter_eq_centroid`：circumcenter_eq_centroid (s : S
implex Real P 1) : s.circumcenter = Finset.univ.centroid Real s.points
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
（共 123 条，此处仅展示前 30 条）
-/
theorem midpoint_faceOppositeCentroid_eulerPoint {n : ℕ} [hn : NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    midpoint ℝ (s.faceOppositeCentroid i) (s.eulerPoint i) = s.ninePointCircle.center := by
  apply vsub_left_cancel (p := s.circumcenter)
  rw [ninePointCircle_center, midpoint_vsub, vadd_vsub, eulerPoint,
    mongePoint_eq_smul_vsub_vadd_circumcenter, ← centroid]
  by_cases hn1 : n = 1
  · obtain rfl := hn1
    suffices (2⁻¹ : ℝ) • (s.faceOppositeCentroid i -ᵥ s.centroid) +
        (2⁻¹ : ℝ) • (s.points i -ᵥ s.centroid) = 0 by
      simpa [circumcenter_eq_centroid, centroid]
    rw [faceOppositeCentroid_vsub_centroid_eq_smul_vsub, ← smul_add]
    exact (smul_eq_zero_of_right _ (by simp))
  have hltn : 1 < n := by
    have _ := hn.out
    lia
  have hnsub1 : (n - 1 : ℕ) = (n : ℝ) - 1 := by
    push_cast [hltn]
    rfl
  rw [vadd_vadd, vadd_vsub, vsub_vadd_eq_vsub_sub, smul_sub, sub_add, smul_smul, ← sub_smul,
    ← sub_one_mul, show ((n : ℝ)⁻¹ - 1) = -(n - 1) / n by field [hn.out],
    neg_div, neg_mul, hnsub1, div_mul_div_cancel₀' (by simpa [sub_eq_zero] using hn1),
    neg_smul, sub_neg_eq_add, faceOppositeCentroid_eq_smul_vsub_vadd_point,
    ← smul_add, vadd_vsub_assoc, add_add_add_comm, ← smul_add, vsub_add_vsub_cancel, ← add_assoc]
  push_cast
  have : (n : ℝ)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) =
      (((n + 1) / n : ℝ)) • (s.centroid -ᵥ s.circumcenter) := by
    rw [add_comm (n : ℝ) 1, add_div, div_self (by simpa using hn.out), add_smul, one_smul, one_div]
  rw [this, ← two_smul ℝ, smul_smul]
  norm_num
/-
**Affine.Simplex.isDiameter_ninePointCircle** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：isDiameter_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n) (i 
: Fin (n + 1)) : s.ninePointCircle.IsDiameter (s.faceOppositeCentroid i) (s.eule
rPoint i) where left_mem
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`：faceOppositeCen
troid_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (
n + 1)) : s.faceOppositeCentroid i in s.nineP…
· 使用定理 `Affine.Simplex.midpoint_faceOppositeCentroid_eulerPoint`：midpoint_faceOp
positeCentroid_eulerPoint {n : Nat} [hn : NeZero n] (s : Simplex Real P n) (i : 
Fin (n + 1)) : midpoint Real (s.faceOppositeC…
-/
theorem isDiameter_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.ninePointCircle.IsDiameter (s.faceOppositeCentroid i) (s.eulerPoint i) where
  left_mem := s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i
/-
**Affine.Simplex.eulerPoint_mem_ninePointCircle** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：eulerPoint_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n)
 (i : Fin (n + 1)) : s.eulerPoint i in s.ninePointCircle
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsDiameter.right_mem`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAddTorso…
· 使用定理 `Affine.Simplex.isDiameter_ninePointCircle`：isDiameter_ninePointCircle {n
 : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : s.ninePointCircle.
IsDiameter (s.faceOppositeCentr…
-/
theorem eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.eulerPoint i ∈ s.ninePointCircle :=
  (s.isDiameter_ninePointCircle i).right_mem
/-
**Affine.Simplex.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle** 是 Mat
hlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle {n : Nat} [NeZero 
n] (s : Simplex Real P n) (i : Fin (n + 1)) : ((s.faceOpposite i).orthogonalProj
ectionSpan (s.eulerPoint i)).val in s.ninePointCircle
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.thales_theorem`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.isDiameter_ninePointCircle`：isDiameter_ninePointCircle {n
 : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : s.ninePointCircle.
IsDiameter (s.faceOppositeCentr…
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `EuclideanGeometry.angle_orthogonalProjection_self`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Affine.Simplex.faceOppositeCentroid_mem_affineSpan_face`：faceOppositeCen
troid_mem_affineSpan_face [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s
.faceOppositeCentroid i in affineSpan k (Set.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n]
    (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    ((s.faceOpposite i).orthogonalProjectionSpan (s.eulerPoint i)).val ∈ s.ninePointCircle := by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i), orthogonalProjectionSpan]
  exact angle_orthogonalProjection_self _ <| faceOppositeCentroid_mem_affineSpan_face s i

end Affine.Simplex

namespace Affine.Triangle

/-
**Affine.Triangle.eulerPoint_eq_midpoint** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Trian
gle`。
形式化陈述：eulerPoint_eq_midpoint (s : Triangle Real P) (i : Fin 3) : s.eulerPoint i 
= midpoint Real s.orthocenter (s.points i)
参数：s : Triangle Real P；i : Fin 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_right_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [
T : AddTorsor G P] {p₁ p₂ p : P}, p -ᵥ p₁ = p -ᵥ p₂ → p₁ = p₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `Affine.Simplex.points_vsub_eulerPoint`：points_vsub_eulerPoint {n : Nat} 
(s : Simplex Real P n) (i : Fin (n + 1)) : s.points i -ᵥ s.eulerPoint i = ((n - 
1) / n : Real) • (s.points …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `vsub_midpoint`：vsub_midpoint (p₁ p₂ p : P) : p -ᵥ midpoint R p₁ p₂ = (⅟2
 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem eulerPoint_eq_midpoint (s : Triangle ℝ P) (i : Fin 3) :
    s.eulerPoint i = midpoint ℝ s.orthocenter (s.points i) := by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint, Simplex.points_vsub_eulerPoint, vsub_midpoint]
  norm_num
/-
**Affine.Triangle.altitudeFoot_mem_ninePointCircle** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Triangle`。
形式化陈述：altitudeFoot_mem_ninePointCircle (s : Triangle Real P) (i : Fin 3) : s.alt
itudeFoot i in s.ninePointCircle
参数：s : Triangle Real P；i : Fin 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.altitudeFoot.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.orthogonalProjection_eq_orthogonalProjection_iff_vsub_
mem`：orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem {s : AffineSubspa
ce 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p q :…
· 使用定理 `Affine.Simplex.points_vsub_eulerPoint`：points_vsub_eulerPoint {n : Nat} 
(s : Simplex Real P n) (i : Fin (n + 1)) : s.points i -ᵥ s.eulerPoint i = ((n - 
1) / n : Real) • (s.points …
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_eq_false`：∀ {α : Type u_1} [inst : Semiring
 α] [CharZero α] {a b : α} {na nb da db : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n
a da →     Mathlib.Meta.Nor…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Affine.Triangle.orthocenter_eq_mongePoint`：orthocenter_eq_mongePoint (t 
: Triangle Real P) : t.orthocenter = t.mongePoint
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Affine.Simplex.mem_altitude`：mem_altitude {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.points i in s.altitude i
（共 34 条，此处仅展示前 30 条）
-/
theorem altitudeFoot_mem_ninePointCircle (s : Triangle ℝ P) (i : Fin 3) :
    s.altitudeFoot i ∈ s.ninePointCircle := by
  convert! s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem,
    Simplex.points_vsub_eulerPoint, Submodule.smul_mem_iff _ (by norm_num),
    ← orthocenter_eq_mongePoint, direction_affineSpan, Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

end Affine.Triangle

end

