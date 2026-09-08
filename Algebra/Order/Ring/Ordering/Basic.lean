/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Ring orderings

We prove basic properties of (pre)orderings on rings and their supports.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {P : RingPreordering R}

/-!
### Preorderings
-/

namespace RingPreordering

@[gcongr]
/-
**RingPreordering.toSubsemiring_le_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Preordering`。
形式化陈述：toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} : P₁.toSubsemir
ing <= P₂.toSubsemiring ↔ P₁ <= P₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

@[gcongr]
/-
**RingPreordering.toSubsemiring_lt_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Preordering`。
形式化陈述：toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} : P₁.toSubsemir
ing < P₂.toSubsemiring ↔ P₁ < P₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

@[mono]
/-
**RingPreordering.toSubsemiring_mono** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`
。
形式化陈述：toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

@[mono]
/-
**RingPreordering.toSubsemiring_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `RingPreord
ering`。
形式化陈述：toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R -
> _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
/-
**RingPreordering.unitsInv_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：unitsInv_mem {a : Rˣ} (ha : ↑a in P) : ↑a⁻¹ in P
参数：ha : ↑a in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `RingPreordering.mem_of_isSquare`：∀ {R : Type u_1} [inst : CommRing R] (P
 : RingPreordering R) {x : R}, IsSquare x → x ∈ P
· 使用引理 `IsSquare.mul_self`：IsSquare.mul_self (r : α) : IsSquare (r * r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
-/
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
/-
**RingPreordering.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a in P
) : a⁻¹ in P
参数：ha : a in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_subst`：eq_div_of_subst {M : Type*} [D
iv M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n) (hd : l_d = d) : l 
= n / d
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'`：cons_eq_div_of_eq_di
v' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.
eval / t_d.eval) : ((-n, e) ::ᵣ t).eval …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
-/
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
/-
**RingPreordering.mem_of_isSumSq** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：mem_of_isSumSq {x : R} (hx : IsSumSq x) : x in P
参数：hx : IsSumSq x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.rec'`：IsSumSq.rec' [Mul R] [Add R] [Zero R] {motive : (s : R) ->
 (h : IsSumSq s) -> Prop} (zero : motive 0 zero) (sq_add : forall {x s}, (hx : I
sS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `RingPreordering.mem_of_isSquare`：∀ {R : Type u_1} [inst : CommRing R] (P
 : RingPreordering R) {x : R}, IsSquare x → x ∈ P
-/
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/-- Construct a preordering from a minimal set of axioms. -/
/-
**RingPreordering.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RingPreordering`。
形式化陈述：mk' {R : Type*} [CommRing R] (P : Set R) (add : forall {x y : R}, x in P -
> y in P -> x + y in P) (mul : forall {x y : R}, x in P -> y in P -> x * y in P)
 (sq : forall x : R, x * x in P) (neg_one : -1 ∉ P) : RingPreordering R where ca
rrier
参数：P : Set R；add : forall {x y : R}, x in P -> y in P -> x + y in P；mul : forall
 {x y : R}, x in P -> y in P -> x * y in P；sq : forall x : R, x * x in P；neg_one
 : -1 ∉ P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a preordering from a minimal set of axioms.
-/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq : ∀ x : R, x * x ∈ P)
    (neg_one : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1
/-
**RingPreordering.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {P : Set R} {add : ∀ {x y : R}, x ∈ P
 → y ∈ P → x + y ∈ P}   {mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P} {sq : ∀ (
x : R), x * x ∈ P} {neg_one : -1 ∉ P} {x : R},   x ∈ RingPreordering.mk' P add m
ul sq neg_one ↔ x ∈ P
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl
/-
**RingPreordering.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {P : Set R} {add : ∀ {x y : R}, x ∈ P
 → y ∈ P → x + y ∈ P}   {mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P} {sq : ∀ (
x : R), x * x ∈ P} {neg_one : -1 ∉ P},   ↑(RingPreordering.mk' P add mul sq neg_
one) = P
参数：x : R；RingPreordering.mk' P add mul sq neg_one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

/-!
### Supports
-/

section ne_top

variable (P)

/-
**RingPreordering.one_notMem_supportAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `RingP
reordering`。
形式化陈述：one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.neg_one_notMem`：∀ {R : Type u_1} [inst : CommRing R] (P 
: RingPreordering R), -1 ∉ P
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2
/-
**RingPreordering.one_notMem_support** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`
。
形式化陈述：one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `RingPreordering.one_notMem_supportAddSubgroup`：one_notMem_supportAddSubg
roup : 1 ∉ P.supportAddSubgroup
-/
theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P
/-
**RingPreordering.supportAddSubgroup_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `RingPreor
dering`。
形式化陈述：supportAddSubgroup_ne_top : P.supportAddSubgroup != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.neg_one_notMem`：∀ {R : Type u_1} [inst : CommRing R] (P 
: RingPreordering R), -1 ∉ P
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2
/-
**RingPreordering.support_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：support_ne_top [P.HasIdealSupport] : P.support != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingPreordering.supportAddSubgroup_ne_top`：supportAddSubgroup_ne_top : P
.supportAddSubgroup != ⊤
-/
theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

/-- Constructor for IsOrdering that doesn't require `ne_top'`. -/
/-
**RingPreordering.IsOrdering.mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering.IsOr
dering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R) [inst_1 : Has
MemOrNegMem P],   (∀ {x y : R}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.suppor
t) → P.IsOrdering
参数：P : RingPreordering R；∀ {x y : R}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.
support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.instHasIdealSupportOfHasMemOrNegMem`：∀ {R : Type u_1} [i
nst : CommRing R] {P : RingPreordering R} [HasMemOrNegMem P], P.HasIdealSupport
· 使用定理 `RingPreordering.support_ne_top`：support_ne_top [P.HasIdealSupport] : P.s
upport != ⊤

--- 原说明 ---
Constructor for IsOrdering that doesn't require `ne_top'`.
-/
theorem IsOrdering.mk' [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

/-
**RingPreordering.HasIdealSupport.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreord
ering.HasIdealSupport`。
形式化陈述：smul_mem [P.HasIdealSupport] (x : R) {a : R} (h₁a : a in P) (h₂a : -a in P
) : x * a in P
参数：x : R；h₁a : a in P；h₂a : -a in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingPreordering.hasIdealSupport_iff`：hasIdealSupport_iff : P.HasIdealSup
port ↔ forall x a : R, a in P -> -a in P -> x * a in P ∧ -(x * a) in P where mp 
_
-/
theorem smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]
/-
**RingPreordering.HasIdealSupport.neg_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPr
eordering.HasIdealSupport`。
形式化陈述：neg_smul_mem [P.HasIdealSupport] (x : R) {a : R} (h₁a : a in P) (h₂a : -a 
in P) : -(x * a) in P
参数：x : R；h₁a : a in P；h₂a : -a in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingPreordering.hasIdealSupport_iff`：hasIdealSupport_iff : P.HasIdealSup
port ↔ forall x a : R, a in P -> -a in P -> x * a in P ∧ -(x * a) in P where mp 
_
-/
theorem neg_smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

/-
**RingPreordering.hasIdealSupport_of_isUnit_two** 是 Mathlib 中的一个定理，位于命名空间 `RingP
reordering`。
形式化陈述：hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport
参数：h : IsUnit (2 : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingPreordering.hasIdealSupport_iff`：hasIdealSupport_iff : P.HasIdealSup
port ↔ forall x a : R, a in P -> -a in P -> x * a in P ∧ -(x * a) in P where mp 
_
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 85 条，此处仅展示前 30 条）
-/
theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

variable {P} in
@[aesop unsafe 70% apply]
/-
**RingPreordering.eq_zero_of_mem_of_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreor
dering`。
形式化陈述：∀ {F : Type u_2} [inst : Field F] {P : RingPreordering F} {x : F}, x ∈ P →
 -x ∈ P → x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `RingPreordering.inv_mem`：inv_mem {F : Type*} [Field F] {P : RingPreorder
ing F} {a : F} (ha : a in P) : a⁻¹ in P
· 使用定理 `RingPreordering.neg_one_notMem`：∀ {R : Type u_1} [inst : CommRing R] (P 
: RingPreordering R), -1 ∉ P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem
/-
**RingPreordering.supportAddSubgroup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingPreor
dering`。
形式化陈述：supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingPreordering.eq_zero_of_mem_of_neg_mem`：∀ {F : Type u_2} [inst : Fiel
d F] {P : RingPreordering F} {x : F}, x ∈ P → -x ∈ P → x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]
/-
**RingPreordering.support_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {F : Type u_2} [inst : Field F] (P : RingPreordering F), P.support = ⊥
参数：P : RingPreordering F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.instHasIdealSupport`：∀ {F : Type u_2} [inst : Field F] (
P : RingPreordering F), P.HasIdealSupport
· 使用定理 `RingPreordering.supportAddSubgroup_eq_bot`：supportAddSubgroup_eq_bot : P
.supportAddSubgroup = ⊥
-/
@[simp] theorem support_eq_bot : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.support.IsPrime := by simpa using Ideal.isPrime_bot

end Field

/-
**RingPreordering.isOrdering_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：isOrdering_iff : P.IsOrdering ↔ forall a b : R, -(a * b) in P -> a in P ∨ 
b in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingPreordering.instSubsemiringClass`：∀ (R : Type u_1) [inst : CommRing 
R], SubsemiringClass (RingPreordering R) R
· 使用定理 `HasMemOrNegMem.neg_mem_of_notMem`：∀ {S : Type u_3} {G : Type u_4} [inst 
: Neg G] [inst_1 : SetLike S G] (s : S) [HasMemOrNegMem s], ∀ x ∉ s, -x ∈ s
· 使用定理 `RingPreordering.IsOrdering.toHasMemOrNegMem`：∀ {R : Type u_1} {inst : Co
mmRing R} {P : RingPreordering R} [self : P.IsOrdering], HasMemOrNegMem P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RingPreordering.instHasIdealSupportOfHasMemOrNegMem`：∀ {R : Type u_1} [i
nst : CommRing R] {P : RingPreordering R} [HasMemOrNegMem P], P.HasIdealSupport
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `RingPreordering.IsOrdering.toIsPrime`：∀ {R : Type u_1} {inst : CommRing 
R} {P : RingPreordering R} [self : P.IsOrdering], P.support.IsPrime
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `RingPreordering.IsOrdering.mk'`：∀ {R : Type u_1} [inst : CommRing R] (P 
: RingPreordering R) [inst_1 : HasMemOrNegMem P],   (∀ {x y : R}, x * y ∈ P.supp
ort → x ∈ P.support …
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
（共 33 条，此处仅展示前 30 条）
-/
theorem isOrdering_iff :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [mem_support]
end RingPreordering

