/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Combinatorics.Additive.Corner.Defs
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem on arithmetic progressions of length three.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

@[expose] public section

open Finset SimpleGraph TripartiteFromTriangles
open Function hiding graph
open Fintype (card)

variable {G : Type*} [AddCommGroup G] {A : Finset (G × G)} {a b c : G} {n : ℕ} {ε : ℝ}

namespace Corners

/-- The triangle indices for the proof of the corners theorem construction. -/
/-
**Corners.triangleIndices** 是 Mathlib 中的一个定义，位于命名空间 `Corners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle indices for the proof of the corners theorem construction.
-/
private def triangleIndices (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun (a, b) ↦ (a, b, a + b), by rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩

@[simp]
/-
**Corners.mk_mem_triangleIndices** 是 Mathlib 中的一个引理，位于命名空间 `Corners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mk_mem_triangleIndices : (a, b, c) ∈ triangleIndices A ↔ (a, b) ∈ A ∧ c = a + b := by
  simp only [triangleIndices, Prod.ext_iff, mem_map, Prod.exists, eq_comm]
  refine ⟨?_, fun h ↦ ⟨_, _, h.1, rfl, rfl, h.2⟩⟩
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩
  exact ⟨h₁, h₂⟩
/-
**Corners.card_triangleIndices** 是 Mathlib 中的一个引理，位于命名空间 `Corners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma card_triangleIndices : #(triangleIndices A) = #A := card_map _
/-
**Corners.triangleIndices.instExplicitDisjoint** 是 Mathlib 中的一个实例，位于命名空间 `Corner
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance triangleIndices.instExplicitDisjoint : ExplicitDisjoint (triangleIndices A) := by
  constructor <;> simp +contextual
/-
**Corners.noAccidental** 是 Mathlib 中的一个引理，位于命名空间 `Corners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma noAccidental (hs : IsCornerFree (A : Set (G × G))) :
    NoAccidental (triangleIndices A) where
  eq_or_eq_or_eq a a' b b' c c' ha hb hc := by
    simp only [mk_mem_triangleIndices] at ha hb hc
    exact .inl <| hs ⟨hc.1, hb.1, ha.1, hb.2.symm.trans ha.2⟩
/-
**Corners.farFromTriangleFree_graph** 是 Mathlib 中的一个引理，位于命名空间 `Corners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma farFromTriangleFree_graph [Fintype G] [DecidableEq G] (hε : ε * card G ^ 2 ≤ #A) :
    (graph <| triangleIndices A).FarFromTriangleFree (ε / 9) := by
  refine farFromTriangleFree _ ?_
  simp_rw [card_triangleIndices, mul_comm_div, Nat.cast_pow, Nat.cast_add]
  ring_nf
  simpa only [mul_comm] using hε

end Corners

variable [Fintype G]

open Corners


/-- An explicit form for the constant in the corners theorem.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exponential. This means
`cornersTheoremBound` is in practice absolutely tiny. -/
/-
**cornersTheoremBound** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cornersTheoremBound (ε : Real) : Nat
参数：ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An explicit form for the constant in the corners theorem.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exp
onential. This means
`cornersTheoremBound` is in practice absolutely tiny.
-/
noncomputable def cornersTheoremBound (ε : ℝ) : ℕ := ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1

/-- The **corners theorem** for finite abelian groups.

The maximum density of a corner-free set in `G × G` goes to zero as `|G|` tends to infinity. -/
/-
**corners_theorem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：corners_theorem (ε : Real) (hε : 0 < ε) (hG : cornersTheoremBound ε <= car
d G) (A : Finset (G × G)) (hAε : ε * card G ^ 2 <= #A) : ¬ IsCornerFree (A : Set
 (G × G))
参数：ε : Real；hε : 0 < ε；hG : cornersTheoremBound ε <= card G；A : Finset (G × G)；h
Aε : ε * card G ^ 2 <= #A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_le_iff_le_one_left`：mul_le_iff_le_one_left [MulPosMono α] [MulPosRef
lectLE α] (b0 : 0 < b) : a * b <= b ↔ a <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `_private.Mathlib.Combinatorics.Additive.Corner.Roth.0.Corners.noAccident
al`：∀ {G : Type u_1} [inst : AddCommGroup G] {A : Finset (G × G)},   IsCornerFre
e ↑A → SimpleGraph.TripartiteFromTriangles.NoAccidental (Corners…
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `inv_lt_iff_one_lt_mul₀'`：inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b 
↔ 1 < a * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `SimpleGraph.triangleRemovalBound_pos`：triangleRemovalBound_pos (hε : 0 <
 ε) : 0 < triangleRemovalBound ε
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
The **corners theorem** for finite abelian groups.

The maximum density of a corner-free set in `G × G` goes to zero as `|G|` tends 
to infinity.
-/
theorem corners_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset (G × G)) (hAε : ε * card G ^ 2 ≤ #A) : ¬ IsCornerFree (A : Set (G × G)) := by
  rintro hA
  rw [cornersTheoremBound, Nat.add_one_le_iff] at hG
  have hε₁ : ε ≤ 1 := by
    have := hAε.trans (Nat.cast_le.2 A.card_le_univ)
    simp only [sq, Nat.cast_mul, Fintype.card_prod] at this
    rwa [mul_le_iff_le_one_left] at this
    positivity
  have := noAccidental hA
  rw [Nat.floor_lt' (by positivity), inv_lt_iff_one_lt_mul₀' (by positivity)] at hG
  refine hG.not_ge (le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < card G ^ 2))
  classical
  have h₁ := (farFromTriangleFree_graph hAε).le_card_cliqueFinset
  rw [card_triangles, card_triangleIndices] at h₁
  convert! h₁.trans (Nat.cast_le.2 <| card_le_univ _) using 1 <;> simp <;> ring

open Fin.NatCast in -- TODO: refactor to avoid needing the coercion
/-- The **corners theorem** for `ℕ`.

The maximum density of a corner-free set in `{1, ..., n} × {1, ..., n}` goes to zero as `n` tends to
infinity. -/
/-
**corners_theorem_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：corners_theorem_nat (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) <= n) (
A : Finset (Nat × Nat)) (hAn : A subseteq range n ×ˢ range n) (hAε : ε * n ^ 2 <
= #A) : ¬ IsCornerFree (A : Set (Nat × Nat))
参数：hε : 0 < ε；hn : cornersTheoremBound (ε / 9) <= n；A : Finset (Nat × Nat)；hAn :
 A subseteq range n ×ˢ range n；hAε : ε * n ^ 2 <= #A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Fin.isAddFreimanIso_Iio`：isAddFreimanIso_Iio (hm : m != 0) (hkmn : m * k
 <= n) : IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `IsCornerFree.of_image`：IsCornerFree.of_image (hf : IsAddFreimanHom 2 s t
 f) (hf' : s.InjOn f) (hAs : (A : Set (G × G)) subseteq s ×ˢ s) (hA : IsCornerFr
ee (Prod.ma…
· 使用定理 `IsAddFreimanIso.isAddFreimanHom`：∀ {α : Type u_2} {β : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : AddCommMonoid β] {A : Set α} {B : Set β} {f : α → β}
   {n : ℕ}, IsAddFrei…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Fin.natCast_strictMono`：natCast_strictMono (hbn : b <= n) (hab : a < b) 
: (a : Fin (n + 1)) < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 101 条，此处仅展示前 30 条）

--- 原说明 ---
The **corners theorem** for `ℕ`.

The maximum density of a corner-free set in `{1, ..., n} × {1, ..., n}` goes to 
zero as `n` tends to
infinity.
-/
theorem corners_theorem_nat (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) ≤ n)
    (A : Finset (ℕ × ℕ)) (hAn : A ⊆ range n ×ˢ range n) (hAε : ε * n ^ 2 ≤ #A) :
    ¬ IsCornerFree (A : Set (ℕ × ℕ)) := by
  rintro hA
  rw [← coe_subset, coe_product] at hAn
  have : A = Prod.map Fin.val Fin.val ''
      (Prod.map Nat.cast Nat.cast '' A : Set (Fin (2 * n).succ × Fin (2 * n).succ)) := by
    rw [Set.image_image, Set.image_congr, Set.image_id]
    simp only [mem_coe, Nat.succ_eq_add_one, Prod.map_apply, Fin.val_natCast, id_eq, Prod.forall,
      Prod.mk.injEq, Nat.mod_succ_eq_iff_lt]
    rintro a b hab
    have := hAn hab
    simp at this
    lia
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom Fin.val_injective.injOn <| by
    refine Set.image_subset_iff.2 <| hAn.trans fun x hx ↦ ?_
    simp only [coe_range, Set.mem_prod, Set.mem_Iio] at hx
    exact ⟨Fin.natCast_strictMono (by lia) hx.1, Fin.natCast_strictMono (by lia) hx.2⟩
  rw [← coe_image] at this
  refine corners_theorem (ε / 9) (by positivity) (by simp; lia) _ ?_ this
  calc
    _ = ε / 9 * (2 * n + 1) ^ 2 := by simp
    _ ≤ ε / 9 * (2 * n + n) ^ 2 := by gcongr; simp; unfold cornersTheoremBound at hn; lia
    _ = ε * n ^ 2 := by ring
    _ ≤ #A := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      have : Set.InjOn Nat.cast (range n) :=
        (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono (by simp; lia)
      exact (this.prodMap this).mono hAn

/-- **Roth's theorem** for finite abelian groups.

The maximum density of a 3AP-free set in `G` goes to zero as `|G|` tends to infinity. -/
/-
**roth_3ap_theorem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：roth_3ap_theorem (ε : Real) (hε : 0 < ε) (hG : cornersTheoremBound ε <= ca
rd G) (A : Finset G) (hAε : ε * card G <= #A) : ¬ ThreeAPFree (A : Set G)
参数：ε : Real；hε : 0 < ε；hG : cornersTheoremBound ε <= card G；A : Finset G；hAε : ε
 * card G <= #A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
**Roth's theorem** for finite abelian groups.

The maximum density of a 3AP-free set in `G` goes to zero as `|G|` tends to infi
nity.
-/
theorem roth_3ap_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset G) (hAε : ε * card G ≤ #A) : ¬ ThreeAPFree (A : Set G) := by
  rintro hA
  classical
  let B : Finset (G × G) := univ.filter fun (x, y) ↦ y - x ∈ A
  have : ε * card G ^ 2 ≤ #B := by
    calc
      _ = card G * (ε * card G) := by ring
      _ ≤ card G * #A := by gcongr
      _ = #B := ?_
    norm_cast
    rw [← card_univ, ← card_product]
    exact card_equiv ((Equiv.refl _).prodShear fun a ↦ Equiv.addLeft a) (by simp [B])
  obtain ⟨x₁, y₁, x₂, y₂, hx₁y₁, hx₁y₂, hx₂y₁, hxy, hx₁x₂⟩ :
      ∃ x₁ y₁ x₂ y₂, y₁ - x₁ ∈ A ∧ y₂ - x₁ ∈ A ∧ y₁ - x₂ ∈ A ∧ x₁ + y₂ = x₂ + y₁ ∧ x₁ ≠ x₂ := by
    simpa [IsCornerFree, isCorner_iff, B, -exists_and_left, -exists_and_right]
      using corners_theorem ε hε hG B this
  have := hA hx₂y₁ hx₁y₁ hx₁y₂ <| by -- TODO: This really ought to just be `by linear_combination h`
    rw [sub_add_sub_comm, add_comm, add_sub_add_comm, add_right_cancel_iff,
      sub_eq_sub_iff_add_eq_add, add_comm, hxy, add_comm]
  exact hx₁x₂ <| by simpa using this.symm

open Fin.NatCast in -- TODO: refactor to avoid needing the coercion
/-- **Roth's theorem** for `ℕ`.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends to infinity. -/
/-
**roth_3ap_theorem_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：roth_3ap_theorem_nat (ε : Real) (hε : 0 < ε) (hG : cornersTheoremBound (ε 
/ 3) <= n) (A : Finset Nat) (hAn : A subseteq range n) (hAε : ε * n <= #A) : ¬ T
hreeAPFree (A : Set Nat)
参数：ε : Real；hε : 0 < ε；hG : cornersTheoremBound (ε / 3) <= n；A : Finset Nat；hAn 
: A subseteq range n；hAε : ε * n <= #A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Fin.isAddFreimanIso_Iio`：isAddFreimanIso_Iio (hm : m != 0) (hkmn : m * k
 <= n) : IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ThreeAPFree.of_image`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMon
oid α] [inst_1 : AddCommMonoid β] {s A : Set α} {t : Set β}   {f : α → β}, IsAdd
FreimanHom…
· 使用定理 `IsAddFreimanIso.isAddFreimanHom`：∀ {α : Type u_2} {β : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : AddCommMonoid β] {A : Set α} {B : Set β} {f : α → β}
   {n : ℕ}, IsAddFrei…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Fin.natCast_strictMono`：natCast_strictMono (hbn : b <= n) (hab : a < b) 
: (a : Fin (n + 1)) < b
· 使用定理 `roth_3ap_theorem`：roth_3ap_theorem (ε : Real) (hε : 0 < ε) (hG : corners
TheoremBound ε <= card G) (A : Finset G) (hAε : ε * card G <= #A) : ¬ ThreeAPFre
e (A :…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
**Roth's theorem** for `ℕ`.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends
 to infinity.
-/
theorem roth_3ap_theorem_nat (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound (ε / 3) ≤ n)
    (A : Finset ℕ) (hAn : A ⊆ range n) (hAε : ε * n ≤ #A) : ¬ ThreeAPFree (A : Set ℕ) := by
  rintro hA
  rw [← coe_subset, coe_range] at hAn
  have : A = Fin.val '' (Nat.cast '' A : Set (Fin (2 * n).succ)) := by
    rw [Set.image_image, Set.image_congr, Set.image_id]
    simp only [mem_coe, Nat.succ_eq_add_one, Fin.val_natCast, id_eq, Nat.mod_succ_eq_iff_lt]
    rintro a ha
    have := hAn ha
    simp at this
    lia
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom Fin.val_injective.injOn <| Set.image_subset_iff.2 <|
      hAn.trans fun x hx ↦ Fin.natCast_strictMono (by lia) <| by
        simpa only [coe_range, Set.mem_Iio] using hx
  rw [← coe_image] at this
  refine roth_3ap_theorem (ε / 3) (by positivity) (by simp; lia) _ ?_ this
  calc
    _ = ε / 3 * (2 * n + 1) := by simp
    _ ≤ ε / 3 * (2 * n + n) := by gcongr; simp; unfold cornersTheoremBound at hG; lia
    _ = ε * n := by ring
    _ ≤ #A := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      exact (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono <| hAn.trans <| by
        simp; lia

open Asymptotics Filter

/-- **Roth's theorem** for `ℕ` as an asymptotic statement.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends to infinity. -/
/-
**rothNumberNat_isLittleO_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_isLittleO_id : IsLittleO atTop (fun N => (rothNumberNat N : 
Real)) (fun N => (N : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `rothNumberNat_spec`：rothNumberNat_spec (n : Nat) : exists t subseteq ran
ge n, #t = rothNumberNat n ∧ ThreeAPFree (t : Set Nat)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `roth_3ap_theorem_nat`：roth_3ap_theorem_nat (ε : Real) (hε : 0 < ε) (hG :
 cornersTheoremBound (ε / 3) <= n) (A : Finset Nat) (hAn : A subseteq range n) (
hAε : ε * …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
**Roth's theorem** for `ℕ` as an asymptotic statement.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends
 to infinity.
-/
theorem rothNumberNat_isLittleO_id :
    IsLittleO atTop (fun N ↦ (rothNumberNat N : ℝ)) (fun N ↦ (N : ℝ)) := by
  simp only [isLittleO_iff, eventually_atTop, RCLike.norm_natCast]
  refine fun ε hε ↦ ⟨cornersTheoremBound (ε / 3), fun n hn ↦ ?_⟩
  obtain ⟨A, hs₁, hs₂, hs₃⟩ := rothNumberNat_spec n
  rw [← hs₂, ← not_lt]
  exact fun hδn ↦ roth_3ap_theorem_nat ε hε hn _ hs₁ hδn.le hs₃
