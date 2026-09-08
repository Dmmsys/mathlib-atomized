/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Order.Northcott

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Descent Theorem

We provide a proof of the following result.

Let `G` be a group and `f : G →* G` an endomorphism of `G` that maps every
subgroup of `G` into itself (e.g., `f = fun g ↦ g ^ n` when `G` is commutative).

If there is a finite subset `s : Set G` and there exists a "height" function `h : G → ℝ`
and constants `a, b, c : ℝ` such that
* `s` surjects onto the quotient `G ⧸ f(G)`,
* for all `g ∈ s` and `x : G`, `h x ≤ a * h (g * x) + c`,
* for all `x : G`, `h (f x) ≥ b * h x - c`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b`,

then `G` is finitely generated. See `Group.fg_of_descent` / `AddGroup.fg_of_descent`.

We use this to deduce a more specific version when `G` is commutative and `f` is the `n`th power
endomorphism and finally an even more specific version with `n = 2`, replacing the upper
and lower bound for the height function by the "approximate parallelogram law"
`∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C`.
See `CommGroup.fg_of_descent` / `AddCommGroup.fg_of_descent` and
`CommGroup.fg_of_descent'` / `AddCommGroup.fg_of_descent'`.

This last version is one of the main ingredients of the standard proof of the
**Mordell-Weil Theorem**. It allows to reduce the statement to showing that `G / 2 • G` is finite
(where `G` is the Mordell-Weil group).

We also provide versions that prove that the torsion subgroup is finite under weaker assumptions.

### Implementation note

Replacing `ℝ` by an ordered field (`{R : Type*} [LinearOrder R] [Field R] [IsOrderedRing R]`)
works, but makes the type check quite slow (and `to_additive` needs some  help...).
As the application(s) work with `ℝ`-valued height functions, we think that generalizing
is not really worth the trouble.
-/

public section

open scoped Pointwise

open Subgroup in
/-- If `G` is a group and `f : G →* G` is an endomorphism sending subgroups into themselves,
and if there is a "height function" `h : G → ℝ` with respect to `f` and a finite subset `s`
of `G`, then `G` is finitely generated. -/
@[to_additive /-- If `G` is an additive group and `f : G →+ G` is an endomorphism sending
subgroups into themselves, and if there is a "height function" `h : G → ℝ` with respect
to `f` and a finite subset `s` of `G`, then `G` is finitely generated. -/]
/-
**Group.fg_of_descent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_of_descent {G : Type*} [Group G] {f : G ->* G} (hf : forall U : S
ubgroup G, U.map f <= U) {s : Set G} {h : G -> Real} {a b c : Real} (ha : 0 <= a
) (H₀ : a < b) (hs : s.Finite) (H₁ : s * f.range = .univ) (H₂ : forall g in s, f
orall x, h x <= a * h (g * x) + c) (H₃ : forall x, b * h x - c <= h (f x)) [Nort
hcott h] : FG G
参数：hf : forall U : Subgroup G, U.map f <= U；ha : 0 <= a；H₀ : a < b；hs : s.Finite
；H₁ : s * f.range = .univ；H₂ : forall g in s, forall x, h x <= a * h (g * x) + c
；H₃ : forall x, b * h x - c <= h (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Northcott.exists_min_image`：exists_min_image [LinearOrder β] [Northcott 
h] (s : Set α) (hs : s.Nonempty) : exists a in s, forall a' in s, h a <= h a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `Subgroup.coe_top`：coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ
· 使用定理 `SetLike.coe_ne_coe`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p
 q : A}, ↑p ≠ ↑q ↔ p ≠ q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Subgroup.notMem_of_notMem_closure`：notMem_of_notMem_closure {P : G} (hP 
: P ∉ closure k) : P ∉ k
· 使用定理 `Mathlib.Tactic.FieldSimp.lt_eq_cancel_lt`：lt_eq_cancel_lt {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M] {e₁ e
₂ f₁ f₂ L : M} (H₁ : e₁ = L * …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
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
（共 105 条，此处仅展示前 30 条）
-/
theorem Group.fg_of_descent {G : Type*} [Group G] {f : G →* G} (hf : ∀ U : Subgroup G, U.map f ≤ U)
    {s : Set G} {h : G → ℝ} {a b c : ℝ} (ha : 0 ≤ a) (H₀ : a < b) (hs : s.Finite)
    (H₁ : s * f.range = .univ) (H₂ : ∀ g ∈ s, ∀ x, h x ≤ a * h (g * x) + c)
    (H₃ : ∀ x, b * h x - c ≤ h (f x)) [Northcott h] :
    FG G := by
  set q := QuotientGroup.mk (s := map f ⊤)
  -- Main proof idea: `s` together with elements of sufficiently small "height" `h` generates `G`.
  let S : Set G := s ∪ {x : G | h x ≤ 2 * c / (b - a)}
  let U := closure S
  suffices U = ⊤ from Group.fg_iff.mpr ⟨S, this, hs.union <| Northcott.finite_le _⟩
  by_contra! H -- Assume for contradiction that these elements generate a proper subgroup `U`.
  rw [← SetLike.coe_ne_coe, coe_top, ← Set.nonempty_compl] at H
  -- Then we can find an element `x : G` not in `U` and of minimal height.
  obtain ⟨x, hx₁, hx₂⟩ := Northcott.exists_min_image h Uᶜ H
  -- Now we construct an element `y` of smaller height and not in `U`.
  obtain ⟨g, hg, z, ⟨y, rfl⟩, rfl⟩ := Set.mem_mul.mp <| H₁ ▸ Set.mem_univ x
  have H' : h y < h (g * f y) := by
    suffices a * h (g * f y) + 2 * c < b * h (g * f y) by nlinarith [H₂ g hg (f y), H₃ y]
    suffices 2 * c / (b - a) < h (g * f y) by field_simp [sub_pos.mpr H₀] at this; grind
    suffices g * f y ∉ S by grind
    exact notMem_of_notMem_closure hx₁
  -- To obtain a contradiction, we do cases on whether `y ∈ U`.
  by_cases hy : y ∈ U
  · exact hx₁ <| U.mul_mem (mem_closure_of_mem <| .inl hg) <| hf U <| mem_map_of_mem f hy
  · exact H'.not_ge <| hx₂ y hy

open Subgroup QuotientGroup in
/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / G ^ n` is finite,
* for all `g x : G`, `h x ≤ a * h (g * x) + c g`,
* for all `x : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`, then `G` is finitely generated.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / n • G` is finite,
* for all `g x : G`, `h x ≤ a * h (g + x) + c g`,
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`, then `G` is finitely generated. -/]
/-
**CommGroup.fg_of_descent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.fg_of_descent {G : Type*} [CommGroup G] {n : Nat} {h : G -> Real
} {a b c₀ : Real} {c : G -> Real} (ha : 0 <= a) (H₀ : a < b) (H₁ : (powMonoidHom
 (α
参数：ha : 0 <= a；H₀ : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
· 使用定理 `Set.exists_max_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq_iff_div_mem`：eq_iff_div_mem {N : Subgroup G} [nN : N.No
rmal] {x y : G} : (x : G ⧸ N) = y ↔ x / y in N
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Group.fg_of_descent`：Group.fg_of_descent {G : Type*} [Group G] {f : G ->
* G} (hf : forall U : Subgroup G, U.map f <= U) {s : Set G} {h : G -> Real} {a b
 c : Real…
· 使用定理 `Subgroup.mem_map`：mem_map {f : G ->* N} {K : Subgroup G} {y : N} : y in 
K.map f ↔ exists x in K, f x = y
· 使用定理 `Subgroup.pow_mem`：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x 
: G}, x ∈ K → ∀ (n : ℕ), x ^ n ∈ K
-/
theorem CommGroup.fg_of_descent {G : Type*} [CommGroup G] {n : ℕ} {h : G → ℝ} {a b c₀ : ℝ}
    {c : G → ℝ} (ha : 0 ≤ a) (H₀ : a < b) (H₁ : (powMonoidHom (α := G) n).range.FiniteIndex)
    (H₂ : ∀ g x, h x ≤ a * h (g * x) + c g) (H₃ : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Group.FG G := by
  let f : G →* G := powMonoidHom n
  let q := QuotientGroup.mk (s := f.range)
  let qi : G ⧸ f.range → G := Function.surjInv mk_surjective
  let s : Set G := Set.range qi
  obtain ⟨g, hg₁, hg₂⟩ := s.exists_max_image c s.toFinite <| Set.range_nonempty qi
  have H₁' : s * f.range = .univ := by
    refine Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_mul.mpr ⟨qi (q x), by simp [s], ?_⟩
    conv => enter [1, y]; rw [eq_comm, ← div_eq_iff_eq_mul', SetLike.mem_coe]
    simp only [↓existsAndEq, and_true]
    exact eq_iff_div_mem.mp (Function.surjInv_eq mk_surjective _).symm
  let c' : ℝ := max c₀ (c g)
  have H₃' x : b * h x - c' ≤ h (f x) := by grind [powMonoidHom_apply]
  refine Group.fg_of_descent (fun U u hu ↦ ?_) ha H₀ s.toFinite H₁' (fun g' hg' x ↦ ?_) H₃'
  · obtain ⟨u', hu₁, rfl⟩ := mem_map.mp hu
    exact U.pow_mem hu₁ n
  · grind

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / G ^ 2` is finite,
* `0 ≤ h x` for all `x : G`,
* there is `C : ℝ` such that for all `x y : G`, `|h (x * y) + h(x / y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then `G` is finitely generated.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / 2 • G` is finite,
* `0 ≤ h x` for all `x : G`,
* there is `C : ℝ` such that for all `x y : G`, `|h (x + y) + h(x - y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then `G` is finitely generated. -/]
/-
**CommGroup.fg_of_descent'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.fg_of_descent' {G : Type*} [CommGroup G] {h : G -> Real} {C : Re
al} (H₁ : (powMonoidHom (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CommGroup.fg_of_descent`：CommGroup.fg_of_descent {G : Type*} [CommGroup 
G] {n : Nat} {h : G -> Real} {a b c₀ : Real} {c : G -> Real} (ha : 0 <= a) (H₀ :
 a < b) (H₁ :…
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem CommGroup.fg_of_descent' {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ}
    (H₁ : (powMonoidHom (α := G) 2).range.FiniteIndex) (H₂ : ∀ x, 0 ≤ h x)
    (H₃ : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C) [Northcott h] :
    Group.FG G := by
  have H₃' x : 4 * h x - (h 1 + C) ≤ h (x ^ 2) := by grind [pow_two, div_self']
  have H₂' g x : h x ≤ 2 * h (g * x) + (2 * h g⁻¹ + C) := by grind [mul_inv_cancel_comm]
  exact fg_of_descent (b := 4) (by norm_num) (by norm_num) H₁ H₂' H₃'

/--
If `M` is a monoid and `n : ℕ`, `h : M → ℝ` satisfy
* for all `M : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : M` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the set of elements of finite order in `M` is finite.
-/
@[to_additive /-- If `M` is an additive monoid and `n : ℕ`, `h : M → ℝ` satisfy
* for all `x : M`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : M` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the set of elements of finite order in `M`
is finite. -/]
/-
**Monoid.finite_set_isOfFiniteOrder_of_descent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.finite_set_isOfFiniteOrder_of_descent {M : Type*} [Monoid M] {n : N
at} {h : M -> Real} {b c₀ : Real} (hb : 1 < b) (H : forall x, b * h x - c₀ <= h 
(x ^ n)) [Northcott h] : Finite { x : M | IsOfFinOrder x }
参数：hb : 1 < b；H : forall x, b * h x - c₀ <= h (x ^ n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Northcott.finite_le`：∀ {α : Type u_1} {β : Type u_2} {h : α → β} {inst :
 LE β} [self : Northcott h] (b : β), {a | h a ≤ b}.Finite
· 使用引理 `IsOfFinOrder.finite_powers`：IsOfFinOrder.finite_powers (ha : IsOfFinOrde
r a) : (powers a : Set G).Finite
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem Monoid.finite_set_isOfFiniteOrder_of_descent {M : Type*} [Monoid M] {n : ℕ} {h : M → ℝ}
    {b c₀ : ℝ} (hb : 1 < b) (H : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Finite { x : M | IsOfFinOrder x } := by
  refine (Northcott.finite_le (h := h) (c₀ / (b - 1))).subset fun t ht ↦ ?_
  have : Finite ↥(Submonoid.powers t) := ht.finite_powers
  let C : ℝ := ⨆ g : Submonoid.powers t, h g
  have hC : ∀ g ∈ Submonoid.powers t, h g ≤ C :=
    fun g hg ↦ Finite.le_ciSup (fun g : Submonoid.powers t ↦ h g) ⟨g, hg⟩
  refine (hC t (Submonoid.mem_powers t)).trans ?_
  obtain ⟨t₀, ht₀⟩ : ∃ g : Submonoid.powers t, h g = C := exists_eq_ciSup_of_finite
  rw [le_div_iff₀' (by grind)]
  grind [Submonoid.pow_mem]

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* for all `x : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the torsion subgroup of `G` is finite.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the torsion subgroup of `G` is finite. -/]
/-
**CommGroup.finite_torsion_of_descent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.finite_torsion_of_descent {G : Type*} [CommGroup G] {n : Nat} {h
 : G -> Real} {b c₀ : Real} (hb : 1 < b) (H : forall x, b * h x - c₀ <= h (x ^ n
)) [Northcott h] : Finite (torsion G)
参数：hb : 1 < b；H : forall x, b * h x - c₀ <= h (x ^ n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.finite_set_isOfFiniteOrder_of_descent`：Monoid.finite_set_isOfFini
teOrder_of_descent {M : Type*} [Monoid M] {n : Nat} {h : M -> Real} {b c₀ : Real
} (hb : 1 < b) (H : forall x, b * …
-/
theorem CommGroup.finite_torsion_of_descent {G : Type*} [CommGroup G] {n : ℕ} {h : G → ℝ}
    {b c₀ : ℝ} (hb : 1 < b) (H : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Finite (torsion G) :=
  Monoid.finite_set_isOfFiniteOrder_of_descent hb H

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* there is `C : ℝ` such that for all `x y : G`, `|h (x * y) + h(x / y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then the torsion subgroup of `G` is finite.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* there is `C : ℝ` such that for all `x y : G`, `|h (x + y) + h(x - y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then the torsion subgroup of `G` is finite. -/]
/-
**CommGroup.finite_torsion_of_descent'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.finite_torsion_of_descent' {G : Type*} [CommGroup G] {h : G -> R
eal} {C : Real} (H : forall x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| <= C)
 [Northcott h] : Finite (torsion G)
参数：H : forall x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CommGroup.finite_torsion_of_descent`：CommGroup.finite_torsion_of_descent
 {G : Type*} [CommGroup G] {n : Nat} {h : G -> Real} {b c₀ : Real} (hb : 1 < b) 
(H : forall x, b * h x - …
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem CommGroup.finite_torsion_of_descent' {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ}
    (H : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C) [Northcott h] :
    Finite (torsion G) := by
  have H' x : 4 * h x - (h 1 + C) ≤ h (x ^ 2) := by grind [pow_two, div_self']
  exact finite_torsion_of_descent (b := 4) (by norm_num) H'

end

