/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `IsometryEquiv.toRealLinearIsometryEquivOfMapZero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `toFun` and `invFun`;
* `IsometryEquiv.toRealLinearIsometryEquiv` : given `f : E ≃ᵢ F`, returns a linear isometry
  equivalence `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `IsometryEquiv.toRealAffineIsometryEquiv` : given `f : PE ≃ᵢ PF`, returns an affine isometry
  equivalence `g : PE ≃ᵃⁱ[ℝ] PF` whose underlying `IsometryEquiv` is `f`

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/

@[expose] public section


variable {E PE F PF : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace PE]
  [NormedAddTorsor E PE] [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace PF]
  [NormedAddTorsor F PF]

open Set AffineMap AffineIsometryEquiv

noncomputable section

namespace IsometryEquiv

/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
/-
**IsometryEquiv.midpoint_fixed** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：midpoint_fixed {x y : PE} : forall e : PE ≃ᵢ PE, e x = x -> e y = y -> e (
midpoint Real x y) = midpoint Real x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineIsometryEquiv.dist_pointReflection_fixed`：dist_pointReflection_fix
ed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
· 使用定理 `AffineIsometryEquiv.dist_pointReflection_self_real`：dist_pointReflection
_self_real (x y : P) : dist (pointReflection Real x y) y = 2 * dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineIsometryEquiv.pointReflection_midpoint_left`：pointReflection_midpo
int_left (x y : P) : pointReflection Real (midpoint Real x y) x = y
· 使用定理 `IsometryEquiv.symm_apply_eq`：symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} 
: h.symm y = x ↔ y = h x
· 使用定理 `AffineIsometryEquiv.pointReflection_midpoint_right`：pointReflection_midp
oint_right (x y : P) : pointReflection Real (midpoint Real x y) y = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` a
nd `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur
-Ulam theorem,
see below.
-/
theorem midpoint_fixed {x y : PE} :
    ∀ e : PE ≃ᵢ PE, e x = x → e y = y → e (midpoint ℝ x y) = midpoint ℝ x y := by
  set z := midpoint ℝ x y
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y }
  have : Nonempty s := ⟨⟨IsometryEquiv.refl PE, rfl, rfl⟩⟩
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd : BddAbove (range fun e : s => dist ((e : PE ≃ᵢ PE) z) z) := by
    refine ⟨dist x z + dist x z, forall_mem_range.2 <| Subtype.forall.2 ?_⟩
    rintro e ⟨hx, _⟩
    calc
      dist (e z) z ≤ dist (e z) x + dist x z := dist_triangle (e z) x z
      _ = dist (e x) (e z) + dist x z := by rw [hx, dist_comm]
      _ = dist x z + dist x z := by rw [e.dist_eq x z]
  -- On the other hand, consider the map `f : (E ≃ᵢ E) → (E ≃ᵢ E)`
  -- sending each `e` to `R ∘ e⁻¹ ∘ R ∘ e`, where `R` is the point reflection in the
  -- midpoint `z` of `[x, y]`.
  set R : PE ≃ᵢ PE := (pointReflection ℝ z).toIsometryEquiv
  set f : PE ≃ᵢ PE → PE ≃ᵢ PE := fun e => ((e.trans R).trans e.symm).trans R
  -- Note that `f` doubles the value of `dist (e z) z`
  have hf_dist : ∀ e, dist (f e z) z = 2 * dist (e z) z := by
    intro e
    dsimp only [trans_apply, coe_toIsometryEquiv, f, R]
    rw [dist_pointReflection_fixed, ← e.dist_eq, e.apply_symm_apply,
      dist_pointReflection_self_real, dist_comm]
  -- Also note that `f` maps `s` to itself
  have hf_maps_to : MapsTo f s s := by
    rintro e ⟨hx, hy⟩
    constructor <;> simp [f, R, z, hx, hy, e.symm_apply_eq.2 hx.symm, e.symm_apply_eq.2 hy.symm]
  -- Therefore, `dist (e z) z = 0` for all `e ∈ s`.
  set c := ⨆ e : s, dist ((e : PE ≃ᵢ PE) z) z
  have : c ≤ c / 2 := by
    apply ciSup_le
    rintro ⟨e, he⟩
    simp only [le_div_iff₀' (zero_lt_two' ℝ), ← hf_dist]
    exact le_ciSup h_bdd ⟨f e, hf_maps_to he⟩
  replace : c ≤ 0 := by linarith
  refine fun e hx hy => dist_le_zero.1 (le_trans ?_ this)
  exact le_ciSup h_bdd ⟨e, hx, hy⟩

/-- A bijective isometry sends midpoints to midpoints. -/
/-
**IsometryEquiv.map_midpoint** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：map_midpoint (f : PE ≃ᵢ PF) (x y : PE) : f (midpoint Real x y) = midpoint 
Real (f x) (f y)
参数：f : PE ≃ᵢ PF；x y : PE。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometryEquiv.pointReflection_midpoint_left`：pointReflection_midpo
int_left (x y : P) : pointReflection Real (midpoint Real x y) x = y
· 使用定理 `IsometryEquiv.symm_apply_apply`：symm_apply_apply (h : α ≃ᵢ β) (x : α) : 
h.symm (h x) = x
· 使用定理 `AffineIsometryEquiv.pointReflection_midpoint_right`：pointReflection_midp
oint_right (x y : P) : pointReflection Real (midpoint Real x y) y = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsometryEquiv.midpoint_fixed`：midpoint_fixed {x y : PE} : forall e : PE 
≃ᵢ PE, e x = x -> e y = y -> e (midpoint Real x y) = midpoint Real x y
· 使用定理 `AffineIsometryEquiv.pointReflection_fixed_iff`：pointReflection_fixed_iff
 [Invertible (2 : 𝕜)] {x y : P} : pointReflection 𝕜 x y = y ↔ y = x
· 使用定理 `IsometryEquiv.symm_apply_eq`：symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} 
: h.symm y = x ↔ y = h x
· 使用定理 `AffineIsometryEquiv.pointReflection_self`：pointReflection_self (x : P) :
 pointReflection 𝕜 x x = x
· 使用定理 `AffineIsometryEquiv.coe_toIsometryEquiv`：coe_toIsometryEquiv : ⇑e.toIsom
etryEquiv = e
· 使用定理 `AffineIsometryEquiv.pointReflection_symm`：pointReflection_symm (x : P) :
 (pointReflection 𝕜 x).symm = pointReflection 𝕜 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIsometryEquiv.toIsometryEquiv_symm`：toIsometryEquiv_symm : e.symm.
toIsometryEquiv = e.toIsometryEquiv.symm
· 使用定理 `IsometryEquiv.eq_symm_apply`：eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} 
: x = h.symm y ↔ h x = y

--- 原说明 ---
A bijective isometry sends midpoints to midpoints.
-/
theorem map_midpoint (f : PE ≃ᵢ PF) (x y : PE) : f (midpoint ℝ x y) = midpoint ℝ (f x) (f y) := by
  set e : PE ≃ᵢ PE :=
    ((f.trans <| (pointReflection ℝ <| midpoint ℝ (f x) (f y)).toIsometryEquiv).trans f.symm).trans
      (pointReflection ℝ <| midpoint ℝ x y).toIsometryEquiv
  have hx : e x = x := by simp [e]
  have hy : e y = y := by simp [e]
  have hm := e.midpoint_fixed hx hy
  simp only [e, trans_apply] at hm
  rwa [← eq_symm_apply, ← toIsometryEquiv_symm, pointReflection_symm, coe_toIsometryEquiv,
    coe_toIsometryEquiv, pointReflection_self, symm_apply_eq, @pointReflection_fixed_iff] at hm

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `ContinuousLinearEquiv` first, then a conversion to an `AffineMap`.
-/


/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear isometry equivalence. -/
/-
**IsometryEquiv.toRealLinearIsometryEquivOfMapZero** 是 Mathlib 中的一个定义，位于命名空间 `Is
ometryEquiv`。
形式化陈述：toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) : E ≃ₗᵢ[Rea
l] F
参数：f : E ≃ᵢ F；h0 : f 0 = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vect
or spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear isometry equivalence.
-/
def toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) : E ≃ₗᵢ[ℝ] F :=
  { (AddMonoidHom.ofMapMidpoint ℝ ℝ f h0 f.map_midpoint).toRealLinearMap f.continuous, f with
    norm_map' := fun x => show ‖f x‖ = ‖x‖ by simp only [← dist_zero_right, ← h0, f.dist_eq] }

@[simp]
/-
**IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero** 是 Mathlib 中的一个定理，位于命名空间
 `IsometryEquiv`。
形式化陈述：coe_toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) : ⇑(f.t
oRealLinearIsometryEquivOfMapZero h0) = f
参数：f : E ≃ᵢ F；h0 : f 0 = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = f :=
  rfl

@[simp]
/-
**IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero_symm** 是 Mathlib 中的一个定理，位
于命名空间 `IsometryEquiv`。
形式化陈述：coe_toRealLinearIsometryEquivOfMapZero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) : 
⇑(f.toRealLinearIsometryEquivOfMapZero h0).symm = f.symm
参数：f : E ≃ᵢ F；h0 : f 0 = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRealLinearIsometryEquivOfMapZero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0).symm = f.symm :=
  rfl

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear isometry equivalence. -/
/-
**IsometryEquiv.toRealLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEqu
iv`。
形式化陈述：toRealLinearIsometryEquiv (f : E ≃ᵢ F) : E ≃ₗᵢ[Real] F
参数：f : E ≃ᵢ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vect
or spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear isometry equivalence.
-/
def toRealLinearIsometryEquiv (f : E ≃ᵢ F) : E ≃ₗᵢ[ℝ] F :=
  (f.trans (IsometryEquiv.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by simpa only [sub_eq_add_neg] using! sub_self (f 0))

@[simp]
/-
**IsometryEquiv.toRealLinearIsometryEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Isome
tryEquiv`。
形式化陈述：toRealLinearIsometryEquiv_apply (f : E ≃ᵢ F) (x : E) : (f.toRealLinearIsom
etryEquiv : E -> F) x = f x - f 0
参数：f : E ≃ᵢ F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem toRealLinearIsometryEquiv_apply (f : E ≃ᵢ F) (x : E) :
    (f.toRealLinearIsometryEquiv : E → F) x = f x - f 0 :=
  (sub_eq_add_neg (f x) (f 0)).symm

@[simp]
/-
**IsometryEquiv.toRealLinearIsometryEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
IsometryEquiv`。
形式化陈述：toRealLinearIsometryEquiv_symm_apply (f : E ≃ᵢ F) (y : F) : (f.toRealLinea
rIsometryEquiv.symm : F -> E) y = f.symm (y + f 0)
参数：f : E ≃ᵢ F；y : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRealLinearIsometryEquiv_symm_apply (f : E ≃ᵢ F) (y : F) :
    (f.toRealLinearIsometryEquiv.symm : F → E) y = f.symm (y + f 0) :=
  rfl

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed add-torsors over
normed vector spaces over `ℝ`, then `f` is an affine isometry equivalence. -/
/-
**IsometryEquiv.toRealAffineIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEqu
iv`。
形式化陈述：toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : PE ≃ᵃⁱ[Real] PF
参数：f : PE ≃ᵢ PF。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed add-
torsors over
normed vector spaces over `ℝ`, then `f` is an affine isometry equivalence.
-/
def toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : PE ≃ᵃⁱ[ℝ] PF :=
  AffineIsometryEquiv.mk' f
    ((vaddConst (Classical.arbitrary PE)).trans <|
        f.trans (vaddConst (f <| Classical.arbitrary PE)).symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE) fun p => by simp

@[simp]
/-
**IsometryEquiv.coeFn_toRealAffineIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Isome
tryEquiv`。
形式化陈述：coeFn_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : ⇑f.toRealAffineIsometryEq
uiv = f
参数：f : PE ≃ᵢ PF。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : ⇑f.toRealAffineIsometryEquiv = f :=
  rfl

@[simp]
/-
**IsometryEquiv.coe_toRealAffineIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Isometr
yEquiv`。
形式化陈述：coe_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : f.toRealAffineIsometryEquiv
.toIsometryEquiv = f
参数：f : PE ≃ᵢ PF。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.ext`：ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁
 = h₂
-/
theorem coe_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) :
    f.toRealAffineIsometryEquiv.toIsometryEquiv = f := by
  ext
  rfl

end IsometryEquiv

