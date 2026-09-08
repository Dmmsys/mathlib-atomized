/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Computability.Encoding
public import Mathlib.Logic.Small.List
public import Mathlib.ModelTheory.Syntax
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Encodings and Cardinality of First-Order Syntax

## Main Definitions

- `FirstOrder.Language.Term.encoding` encodes terms as lists.
- `FirstOrder.Language.BoundedFormula.encoding` encodes bounded formulas as lists.

## Main Results

- `FirstOrder.Language.Term.card_le` shows that the number of terms in `L.Term α` is at most
  `max ℵ₀ # (α ⊕ Σ i, L.Functions i)`.
- `FirstOrder.Language.BoundedFormula.card_le` shows that the number of bounded formulas in
  `Σ n, L.BoundedFormula α n` is at most
  `max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card)`.

## TODO

- `Primcodable` instances for terms and formulas, based on the `encoding`s
- Computability facts about term and formula operations, to set up a computability approach to
  incompleteness

-/

@[expose] public section


universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α : Type u'}

open FirstOrder Cardinal

open Computability List Structure Fin

namespace Term

/-- Encodes a term as a list of variables and function symbols. -/
/-
**FirstOrder.Language.Term.listEncode** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → L.Term α → List (α ⊕ (i : ℕ) ×
 L.Functions i)
参数：α ⊕ (i : ℕ) × L.Functions i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Encodes a term as a list of variables and function symbols.
-/
def listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σ i, L.Functions i)::(List.finRange _).flatMap fun i => (ts i).listEncode

/-- Decodes a list of variables and function symbols as a list of terms. -/
/-
**FirstOrder.Language.Term.listDecode** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → List (α ⊕ (i : ℕ) × L.Function
s i) → List (L.Term α)
参数：α ⊕ (i : ℕ) × L.Functions i；L.Term α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decodes a list of variables and function symbols as a list of terms.
-/
def listDecode : List (α ⊕ (Σ i, L.Functions i)) → List (L.Term α)
  | [] => []
  | Sum.inl a::l => (var a)::listDecode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : n ≤ (listDecode l).length then
      (func f (fun i => (listDecode l)[i])) :: (listDecode l).drop n
    else []
/-
**FirstOrder.Language.Term.listDecode_encode_list** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Term`。
形式化陈述：listDecode_encode_list (l : List (L.Term α)) : listDecode (l.flatMap listE
ncode) = l
参数：l : List (L.Term α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.listEncode.eq_1`：∀ {L : FirstOrder.Language} {α
 : Type u'} (i : α), (FirstOrder.Language.var i).listEncode = [Sum.inl i]
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `FirstOrder.Language.Term.listDecode.eq_2`：∀ {L : FirstOrder.Language} {α
 : Type u'} (a : α) (l : List (α ⊕ (i : ℕ) × L.Functions i)),   FirstOrder.Langu
age.Term.listDecode (Sum.inl a…
· 使用定理 `FirstOrder.Language.Term.listEncode.eq_2`：∀ {L : FirstOrder.Language} {α
 : Type u'} (l : ℕ) (f : L.Functions l) (ts : Fin l → L.Term α),   (FirstOrder.L
anguage.func f ts).listEncode …
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `FirstOrder.Language.Term.listDecode.eq_3`：∀ {L : FirstOrder.Language} {α
 : Type u'} (n : ℕ) (f : L.Functions n) (l : List (α ⊕ (i : ℕ) × L.Functions i))
,   FirstOrder.Language.Term.l…
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `FirstOrder.Language.Term.func.injEq`：∀ {L : FirstOrder.Language} {α : Ty
pe u'} {l : ℕ} (_f : L.Functions l) (_ts : Fin l → L.Term α) (l_1 : ℕ)   (_f_1 :
 L.Functions l_1) (_ts_1 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 34 条，此处仅展示前 30 条）
-/
theorem listDecode_encode_list (l : List (L.Term α)) :
    listDecode (l.flatMap listEncode) = l := by
  suffices h : ∀ (t : L.Term α) (l : List (α ⊕ (Σ i, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction l with
    | nil => rfl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | @func n f ts ih =>
    rw [listEncode, cons_append, listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => rfl
      | cons i l' l'ih => rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']

/-- An encoding of terms as lists. -/
@[simps]
/-
**FirstOrder.Language.Term.encoding** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → Computability.Encoding (L.Term
 α) (α ⊕ (i : ℕ) × L.Functions i)
参数：L.Term α；α ⊕ (i : ℕ) × L.Functions i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding of terms as lists.
-/
protected def encoding : Encoding (L.Term α) (α ⊕ (Σ i, L.Functions i)) where
  encode := listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [flatMap_singleton] at h
    simp only [Option.join, h, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]
/-
**FirstOrder.Language.Term.listEncode_injective** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Term`。
形式化陈述：listEncode_injective : Function.Injective (listEncode : L.Term α -> List (
α oplus (Σ i, L.Functions i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computability.Encoding.encode_injective`：∀ {α : Type u_1} {Γ : Type u_2}
 (e : Computability.Encoding α Γ), Function.Injective e.encode
-/
theorem listEncode_injective :
    Function.Injective (listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))) :=
  Term.encoding.encode_injective
/-
**FirstOrder.Language.Term.card_le** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.Term`。
形式化陈述：card_le : #(L.Term α) <= max ℵ₀ #(α oplus (Σ i, L.Functions i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Computability.Encoding.card_le_card_list`：∀ {α : Type u} {Γ : Type v} (e
 : Computability.Encoding α Γ),   Cardinal.lift.{v, u} (Cardinal.mk α) ≤ Cardina
l.lift.{u, v} (Cardinal.mk (Li…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_list_le_max`：mk_list_le_max (α : Type u) : #(List α) <= max 
ℵ₀ #α
-/
theorem card_le : #(L.Term α) ≤ max ℵ₀ #(α ⊕ (Σ i, L.Functions i)) :=
  lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))
/-
**FirstOrder.Language.Term.card_sigma** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：card_sigma : #(Σ n, L.Term (α oplus (Fin n))) = max ℵ₀ #(α oplus (Σ i, L.F
unctions i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup`：sum_le_lift_mk_mul_iSup {ι : Type u} (
f : ι -> Cardinal.{max u v}) : sum f <= lift #ι * ⨆ i, f i
· 使用定理 `Cardinal.mk_nat`：mk_nat : #Nat = ℵ₀
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `FirstOrder.Language.Term.card_le`：card_le : #(L.Term α) <= max ℵ₀ #(α op
lus (Σ i, L.Functions i))
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.mk_fin`：mk_fin (n : Nat) : #(Fin n) = n
（共 57 条，此处仅展示前 30 条）
-/
theorem card_sigma : #(Σ n, L.Term (α ⊕ (Fin n))) = max ℵ₀ #(α ⊕ (Σ i, L.Functions i)) := by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_lift_mk_mul_iSup _).trans ?_
    rw [mk_nat, lift_aleph0, mul_eq_max_of_aleph0_le_left le_rfl, max_le_iff,
      ciSup_le_iff' bddAbove_of_small]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      grw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast, natCast_lt_aleph0]
    · rw [← Cardinal.one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup bddAbove_of_small 1)
      rw [Cardinal.one_le_iff_ne_zero, mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective
        (fun i => ⟨i + 1, var (Sum.inr (last i))⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1, h.2.1⟩]
/-
**FirstOrder.Language.Term.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Term`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Encodable α] [Encodable (Σ i, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    rw [← flatMap_singleton listEncode, listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]
/-
**FirstOrder.Language.Term.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Term`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h1 : Countable α] [h2 : Countable (Σ l, L.Functions l)] : Countable (L.Term α) := by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩
/-
**FirstOrder.Language.Term.small** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.
Term`。
形式化陈述：small [Small.{u} α] : Small.{u} (L.Term α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `FirstOrder.Language.Term.listEncode_injective`：listEncode_injective : Fu
nction.Injective (listEncode : L.Term α -> List (α oplus (Σ i, L.Functions i)))
-/
instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective listEncode_injective

end Term

namespace BoundedFormula

/-- Encodes a bounded formula as a list of symbols. -/
/-
**FirstOrder.Language.BoundedFormula.listEncode** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → {n : ℕ} → L.BoundedFormula α
 n → List ((k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Relations n ⊕ ℕ)
参数：(k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Relations n ⊕ ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Encodes a bounded formula as a list of symbols.
-/
def listEncode : ∀ {n : ℕ},
    L.BoundedFormula α n → List ((Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | _, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, rel R ts => [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++
      (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | _, imp φ₁ φ₂ => (Sum.inr (Sum.inr 0)::φ₁.listEncode) ++ φ₂.listEncode
  | _, all φ => Sum.inr (Sum.inr 1)::φ.listEncode

/-- Applies the `forall` quantifier to an element of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
/-
**FirstOrder.Language.BoundedFormula.sigmaAll** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → (n : ℕ) × L.BoundedFormula α n
 → (n : ℕ) × L.BoundedFormula α n
参数：n : ℕ；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies the `forall` quantifier to an element of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible.
-/
def sigmaAll : (Σ n, L.BoundedFormula α n) → Σ n, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default


@[simp]
/-
**FirstOrder.Language.BoundedFormula.sigmaAll_apply** 是 Mathlib 中的一个引理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：sigmaAll_apply {n} {φ : L.BoundedFormula α (n + 1)} : sigmaAll ⟨n + 1, φ⟩ 
= ⟨n, φ.all⟩
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigmaAll_apply {n} {φ : L.BoundedFormula α (n + 1)} :
    sigmaAll ⟨n + 1, φ⟩ = ⟨n, φ.all⟩ := rfl

/-- Applies `imp` to two elements of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
/-
**FirstOrder.Language.BoundedFormula.sigmaImp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → (n : ℕ) × L.BoundedFormula α
 n → (n : ℕ) × L.BoundedFormula α n → (n : ℕ) × L.BoundedFormula α n
参数：n : ℕ；n : ℕ；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `imp` to two elements of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible.
-/
def sigmaImp : (Σ n, L.BoundedFormula α n) → (Σ n, L.BoundedFormula α n) → Σ n, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ => if h : m = n then ⟨m, φ.imp (Eq.mp (by rw [h]) ψ)⟩ else default

/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
/-
**FirstOrder.Language.BoundedFormula.sigmaImp_apply** 是 Mathlib 中的一个引理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：sigmaImp_apply {n} {φ ψ : L.BoundedFormula α n} : sigmaImp ⟨n, φ⟩ ⟨n, ψ⟩ =
 ⟨n, φ.imp ψ⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Decodes a list of symbols as a list of formulas.
-/
lemma sigmaImp_apply {n} {φ ψ : L.BoundedFormula α n} :
    sigmaImp ⟨n, φ⟩ ⟨n, ψ⟩ = ⟨n, φ.imp ψ⟩ := by
  simp only [sigmaImp, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

/-- Decodes a list of symbols as a list of formulas. -/
/-
**FirstOrder.Language.BoundedFormula.listDecode** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} →     List ((k : ℕ) × L.Term (
α ⊕ Fin k) ⊕ (n : ℕ) × L.Relations n ⊕ ℕ) → List ((n : ℕ) × L.BoundedFormula α n
)
参数：(k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Relations n ⊕ ℕ；(n : ℕ) × L.Bounde
dFormula α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decodes a list of symbols as a list of formulas.
-/
def listDecode :
    List ((Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)) → List (Σ n, L.BoundedFormula α n)
  | Sum.inr (Sum.inr (n + 2))::l => ⟨n, falsum⟩::(listDecode l)
  | Sum.inl ⟨n₁, t₁⟩::Sum.inl ⟨n₂, t₂⟩::l =>
    (if h : n₁ = n₂ then ⟨n₁, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default)::(listDecode l)
  | Sum.inr (Sum.inl ⟨n, R⟩)::Sum.inr (Sum.inr k)::l => (
    if h : ∀ i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome then
        if h' : ∀ i, (Option.get _ (h i)).1 = k then
          ⟨k, BoundedFormula.rel R fun i => Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩
        else default
      else default)::(listDecode (l.drop n))
  | Sum.inr (Sum.inr 0)::l => if h : 2 ≤ (listDecode l).length
    then (sigmaImp (listDecode l)[0] (listDecode l)[1])::(drop 2 (listDecode l))
    else []
  | Sum.inr (Sum.inr 1)::l => if h : 1 ≤ (listDecode l).length
    then (sigmaAll (listDecode l)[0])::(drop 1 (listDecode l))
    else []
  | _ => []
  termination_by l => l.length

@[simp]
/-
**FirstOrder.Language.BoundedFormula.listDecode_encode_list** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：listDecode_encode_list (l : List (Σ n, L.BoundedFormula α n)) : listDecode
 (l.flatMap (fun φ => φ.2.listEncode)) = l
参数：l : List (Σ n, L.BoundedFormula α n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.listEncode.eq_1`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (x : ℕ),   FirstOrder.Language.BoundedFormula.falsum.listE
ncode = [Sum.inr (Sum.inr (x + 2))]
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `FirstOrder.Language.BoundedFormula.listDecode.eq_1`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (n : ℕ)   (l : List ((k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ
) × L.Relations n ⊕ ℕ)),   FirstOrder.La…
· 使用定理 `FirstOrder.Language.BoundedFormula.listEncode.eq_2`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (x : ℕ) (t₁ t₂ : L.Term (α ⊕ Fin x)),   (FirstOrder.Langua
ge.BoundedFormula.equal t₁ t₂).listEncod…
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `FirstOrder.Language.BoundedFormula.listDecode.eq_2`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (n₁ : ℕ) (t₁ : L.Term (α ⊕ Fin n₁)) (n₂ : ℕ) (t₂ : L.Term 
(α ⊕ Fin n₂))   (l : List ((k : ℕ) × L.T…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `FirstOrder.Language.BoundedFormula.listEncode.eq_3`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (x l : ℕ) (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fi
n x)),   (FirstOrder.Language.BoundedFor…
· 使用定理 `FirstOrder.Language.BoundedFormula.listDecode.eq_3`：∀ {L : FirstOrder.La
nguage} {α : Type u'} (n : ℕ) (R : L.Relations n) (k : ℕ)   (l : List ((k : ℕ) ×
 L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Relati…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.getElem?_eq_some_iff`：∀ {α : Type u_1} {i : ℕ} {a : α} {l : List α}
, l[i]? = some a ↔ ∃ (h : i < l.length), l[i] = a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `List.getElem_append_left`：∀ {α : Type u_1} {i : ℕ} {as bs : List α} (h :
 i < as.length) {h' : i < (as ++ bs).length}, (as ++ bs)[i] = as[i]
（共 72 条，此处仅展示前 30 条）
-/
theorem listDecode_encode_list (l : List (Σ n, L.BoundedFormula α n)) :
    listDecode (l.flatMap (fun φ => φ.2.listEncode)) = l := by
  suffices h : ∀ (φ : Σ n, L.BoundedFormula α n)
      (l' : List ((Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ))),
      (listDecode (listEncode φ.2 ++ l')) = φ::(listDecode l') by
    induction l with
    | nil =>
      simp [listDecode]
    | cons φ l ih => rw [flatMap_cons, h φ _, ih]
  rintro ⟨n, φ⟩
  induction φ with
  | falsum => intro l; rw [listEncode, singleton_append, listDecode]
  | equal =>
    intro l
    rw [listEncode, cons_append, cons_append, listDecode, dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, nil_append]
    · simp only
  | @rel φ_n φ_l φ_R ts =>
    intro l
    rw [listEncode, cons_append, cons_append, singleton_append, cons_append, listDecode]
    have h : ∀ i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σ n, L.BoundedFormula α n).fst, ts i⟩ :
        Σ n, L.Term (α ⊕ (Fin n)))) (finRange φ_l) ++ l))[↑i]?).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, getElem?_fin, id, Option.bind_eq_some_iff,
        getElem?_eq_some_iff, length_append, length_map, length_finRange, exists_eq_right]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [getElem_append_left, getElem_map]
      · simp only [getElem_finRange, cast_mk, Fin.eta, Function.comp_apply, Sum.getLeft?_inl]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Option.join, eq_mp_eq_cast, cons.injEq, Sigma.mk.inj_iff, heq_eq_eq, rel.injEq,
      true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append, length_map, length_finRange, Nat.sub_self, drop, drop_eq_nil_of_le,
      nil_append]
    rw [length_map, length_finRange]
  | imp _ _ ih1 ih2 =>
    intro l
    simp only at *
    rw [listEncode, List.append_assoc, cons_append, listDecode]
    simp only [ih1, ih2, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, getElem_cons_succ, sigmaImp_apply, drop_succ_cons, drop_zero]
  | all _ ih =>
    intro l
    simp only at *
    rw [listEncode, cons_append, listDecode]
    simp only [ih, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, sigmaAll_apply, drop_succ_cons, drop_zero]

/-- An encoding of bounded formulas as lists. -/
@[simps]
/-
**FirstOrder.Language.BoundedFormula.encoding** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} →     Computability.Encoding (
(n : ℕ) × L.BoundedFormula α n) ((k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Rela
tions n ⊕ ℕ)
参数：(n : ℕ) × L.BoundedFormula α n；(k : ℕ) × L.Term (α ⊕ Fin k) ⊕ (n : ℕ) × L.Rel
ations n ⊕ ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An encoding of bounded formulas as lists.
-/
protected def encoding : Encoding (Σ n, L.BoundedFormula α n)
    ((Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)) where
  encode φ := φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    rw [h]
    rfl
/-
**FirstOrder.Language.BoundedFormula.listEncode_sigma_injective** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：listEncode_sigma_injective : Function.Injective fun φ : Σ n, L.BoundedForm
ula α n => φ.2.listEncode
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computability.Encoding.encode_injective`：∀ {α : Type u_1} {Γ : Type u_2}
 (e : Computability.Encoding α Γ), Function.Injective e.encode
-/
theorem listEncode_sigma_injective :
    Function.Injective fun φ : Σ n, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective
/-
**FirstOrder.Language.BoundedFormula.card_le** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.BoundedFormula`。
形式化陈述：card_le : #(Σ n, L.BoundedFormula α n) <= max ℵ₀ (Cardinal.lift.{max u v} 
#α + Cardinal.lift.{u'} L.card)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Computability.Encoding.card_le_card_list`：∀ {α : Type u} {Γ : Type v} (e
 : Computability.Encoding α Γ),   Cardinal.lift.{v, u} (Cardinal.mk α) ≤ Cardina
l.lift.{u, v} (Cardinal.mk (Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_list_eq_max_mk_aleph0`：mk_list_eq_max_mk_aleph0 (α : Type u)
 [Nonempty α] : #(List α) = max #α ℵ₀
· 使用定理 `Sum.nonemptyRight`：∀ {α : Type u} {β : Type v} [h : Nonempty β], Nonempt
y (α ⊕ β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `FirstOrder.Language.Term.card_sigma`：card_sigma : #(Σ n, L.Term (α oplus
 (Fin n))) = max ℵ₀ #(α oplus (Σ i, L.Functions i))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.mk_nat`：mk_nat : #Nat = ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.aleph0_add_aleph0`：aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀
· 使用定理 `FirstOrder.Language.card.eq_1`：∀ (L : FirstOrder.Language), L.card = Car
dinal.mk L.Symbols
· 使用定理 `FirstOrder.Language.Symbols.eq_1`：∀ (L : FirstOrder.Language), L.Symbols
 = ((l : ℕ) × L.Functions l ⊕ (l : ℕ) × L.Relations l)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem card_le : #(Σ n, L.BoundedFormula α n) ≤
    max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card) := by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [mk_list_eq_max_mk_aleph0, lift_max, lift_aleph0, lift_max, lift_aleph0, max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum, Term.card_sigma, mk_sum, ← add_eq_max le_rfl, mk_sum, mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc, add_comm, ← add_assoc, ← add_assoc, aleph0_add_aleph0, add_assoc,
    add_eq_max le_rfl, add_assoc, card, Symbols, mk_sum, lift_add, lift_lift, lift_lift]

section Countable

variable [Countable α] [Countable L.Symbols]

/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (constantsOn α).Symbols := by
  refine mk_le_aleph0_iff.mp ?_
  change (constantsOn α).card ≤ ℵ₀
  simpa only [card_constantsOn, mk_le_aleph0_iff]
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable L[[α]].Symbols := by
  simp only [← mk_le_aleph0_iff]
  change L[[α]].card ≤ ℵ₀
  simp only [withConstants, card_sum, add_le_aleph0, lift_le_aleph0]
  simp only [card, mk_le_aleph0_iff]
  constructor <;> infer_instance
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (Σ n, L.BoundedFormula α n) := by
  refine Cardinal.mk_le_aleph0_iff.mp (BoundedFormula.card_le.trans (max_le (le_refl _) ?_))
  simp only [card, add_le_aleph0, lift_le_aleph0, mk_le_aleph0_iff]
  constructor <;> infer_instance
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (L.Formula α) :=
  (Function.Injective.countable
    (f := fun φ => (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))) <| sigma_mk_injective

end Countable

end BoundedFormula

end Language

end FirstOrder

