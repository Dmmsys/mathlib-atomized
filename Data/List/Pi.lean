/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Multiset.Pi

/-!
# The Cartesian product of lists

## Main definitions

* `List.pi`: Cartesian product of lists indexed by a list.
-/

@[expose] public section

namespace List

namespace Pi
variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*}

/-- Given `α : ι → Sort*`, `Pi.nil α` is the trivial dependent function out of the empty list. -/
/-
**List.Pi.nil** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：nil (α : ι -> Sort*) : (forall i in ([] : List ι), α i)
参数：α : ι -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `α : ι → Sort*`, `Pi.nil α` is the trivial dependent function out of the e
mpty list.
-/
def nil (α : ι → Sort*) : (∀ i ∈ ([] : List ι), α i) :=
  nofun

variable {i : ι} {l : List ι}

/-- Given `f` a function whose domain is `i :: l`, get its value at `i`. -/
/-
**List.Pi.head** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：head (f : forall j in i :: l, α j) : α i
参数：f : forall j in i :: l, α j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l

--- 原说明 ---
Given `f` a function whose domain is `i :: l`, get its value at `i`.
-/
def head (f : ∀ j ∈ i :: l, α j) : α i :=
  f i mem_cons_self

/-- Given `f` a function whose domain is `i :: l`, produce a function whose domain
is restricted to `l`. -/
/-
**List.Pi.tail** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：tail (f : forall j in i :: l, α j) : forall j in l, α j
参数：f : forall j in i :: l, α j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l

--- 原说明 ---
Given `f` a function whose domain is `i :: l`, produce a function whose domain
is restricted to `l`.
-/
def tail (f : ∀ j ∈ i :: l, α j) : ∀ j ∈ l, α j :=
  fun j hj ↦ f j (mem_cons_of_mem _ hj)

variable (i l)

/-- Given `α : ι → Sort*`, a list `l` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `l`, `Pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i :: l`. -/
/-
**List.Pi.cons** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：cons (a : α i) (f : forall j in l, α j) : forall j in i :: l, α j
参数：a : α i；f : forall j in l, α j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `α : ι → Sort*`, a list `l` and a term `i`, as well as a term `a : α i` an
d a
function `f` such that `f j : α j` for all `j` in `l`, `Pi.cons a f` is a functi
on `g` such
that `g k : α k` for all `k` in `i :: l`.
-/
def cons (a : α i) (f : ∀ j ∈ l, α j) : ∀ j ∈ i :: l, α j :=
  Multiset.Pi.cons (α := ι) l _ a f

variable {i l}
/-
**List.Pi.cons_def** 是 Mathlib 中的一个引理，位于命名空间 `List.Pi`。
形式化陈述：cons_def (a : α i) (f : forall j in l, α j) : cons _ _ a f = fun j hj => i
f h : j = i then h.symm.rec a else f j (mem_cons.1 hj).resolve_left h
参数：a : α i；f : forall j in l, α j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cons_def (a : α i) (f : ∀ j ∈ l, α j) : cons _ _ a f =
    fun j hj ↦ if h : j = i then h.symm.rec a else f j <| (mem_cons.1 hj).resolve_left h :=
  rfl
/-
**List.Pi._root_.Multiset.Pi.cons_coe** 是 Mathlib 中的一个引理，位于命名空间 `List.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Multiset.Pi.cons_coe {l : List ι} (a : α i) (f : ∀ j ∈ l, α j) :
    Multiset.Pi.cons l _ a f = cons _ _ a f :=
  rfl
/-
**List.Pi.cons_eta** 是 Mathlib 中的一个定理，位于命名空间 `List.Pi`。
形式化陈述：∀ {ι : Type u_1} [inst : DecidableEq ι] {α : ι → Sort u_2} {i : ι} {l : Li
st ι} (f : (j : ι) → j ∈ i :: l → α j),   List.Pi.cons i l (List.Pi.head f) (Lis
t.Pi.tail f) = f
参数：f : (j : ι) → j ∈ i :: l → α j；List.Pi.head f；List.Pi.tail f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.cons_eta`：cons_eta {m : Multiset α} {a : α} (f : forall a' i
n a ::ₘ m, δ a') : (cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_c
ons_of_mem…
-/
@[simp] lemma cons_eta (f : ∀ j ∈ i :: l, α j) :
    cons _ _ (head f) (tail f) = f :=
  Multiset.Pi.cons_eta (α := ι) (m := l) f
/-
**List.Pi.cons_map** 是 Mathlib 中的一个引理，位于命名空间 `List.Pi`。
形式化陈述：cons_map (a : α i) (f : forall j in l, α j) {α' : ι -> Sort*} (φ : forall 
⦃j⦄, α j -> α' j) : cons _ _ (φ a) (fun j hj => φ (f j hj)) = (fun j hj => φ ((c
ons _ _ a f) j hj))
参数：a : α i；f : forall j in l, α j；φ : forall ⦃j⦄, α j -> α' j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.cons_map`：cons_map (b : δ a) (f : forall a' in m, δ a') {δ' 
: α -> Sort*} (φ : forall ⦃a'⦄, δ a' -> δ' a') : Pi.cons _ _ (φ b) (fun a' ha' =
> φ (f a' …
-/
lemma cons_map (a : α i) (f : ∀ j ∈ l, α j)
    {α' : ι → Sort*} (φ : ∀ ⦃j⦄, α j → α' j) :
    cons _ _ (φ a) (fun j hj ↦ φ (f j hj)) = (fun j hj ↦ φ ((cons _ _ a f) j hj)) :=
  Multiset.Pi.cons_map _ _ _
/-
**List.Pi.forall_rel_cons_ext** 是 Mathlib 中的一个引理，位于命名空间 `List.Pi`。
形式化陈述：forall_rel_cons_ext {r : forall ⦃i⦄, α i -> α i -> Prop} {a₁ a₂ : α i} {f₁
 f₂ : forall j in l, α j} (ha : r a₁ a₂) (hf : forall (i : ι) (hi : i in l), r (
f₁ i hi) (f₂ i hi)) : forall j hj, r (cons _ _ a₁ f₁ j hj) (cons _ _ a₂ f₂ j hj)
参数：ha : r a₁ a₂；hf : forall (i : ι) (hi : i in l), r (f₁ i hi) (f₂ i hi)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.forall_rel_cons_ext`：forall_rel_cons_ext {r : forall ⦃a⦄, δ 
a -> δ a -> Prop} {b₁ b₂ : δ a} {f₁ f₂ : forall a' in m, δ a'} (hb : r b₁ b₂) (h
f : forall (a : α) (h…
-/
lemma forall_rel_cons_ext {r : ∀ ⦃i⦄, α i → α i → Prop} {a₁ a₂ : α i} {f₁ f₂ : ∀ j ∈ l, α j}
    (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ l), r (f₁ i hi) (f₂ i hi)) :
    ∀ j hj, r (cons _ _ a₁ f₁ j hj) (cons _ _ a₂ f₂ j hj) :=
  Multiset.Pi.forall_rel_cons_ext (α := ι) (m := l) ha hf

end Pi

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
/-
**List.pi** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{ι : Type u_1} →   [DecidableEq ι] → {α : ι → Type u_2} → (l : List ι) → (
(i : ι) → List (α i)) → List ((i : ι) → i ∈ l → α i)
参数：l : List ι；(i : ι) → List (α i)；(i : ι) → i ∈ l → α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x`
-/
def pi : ∀ l : List ι, (∀ i, List (α i)) → List (∀ i, i ∈ l → α i)
  | [], _ => [List.Pi.nil α]
  | i :: l, fs => (fs i).flatMap (fun b ↦ (pi l fs).map (List.Pi.cons _ _ b))
/-
**List.pi_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {ι : Type u_1} [inst : DecidableEq ι] {α : ι → Type u_2} (t : (i : ι) → 
List (α i)), [].pi t = [List.Pi.nil α]
参数：t : (i : ι) → List (α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pi_nil (t : ∀ i, List (α i)) :
    pi [] t = [Pi.nil α] :=
  rfl
/-
**List.pi_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {ι : Type u_1} [inst : DecidableEq ι] {α : ι → Type u_2} (i : ι) (l : Li
st ι) (t : (j : ι) → List (α j)),   (i :: l).pi t = List.flatMap (fun b => List.
map (List.Pi.cons i l b) (l.pi t)) (t i)
参数：i : ι；l : List ι；t : (j : ι) → List (α j)；i :: l；fun b => List.map (List.Pi.c
ons i l b) (l.pi t)；t i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pi_cons (i : ι) (l : List ι) (t : ∀ j, List (α j)) :
    pi (i :: l) t = ((t i).flatMap fun b ↦ (pi l t).map <| Pi.cons _ _ b) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**List._root_.Multiset.pi_coe** 是 Mathlib 中的一个引理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Multiset.pi_coe (l : List ι) (fs : ∀ i, List (α i)) :
    (l : Multiset ι).pi (fs ·) = (↑(pi l fs) : Multiset (∀ i ∈ l, α i)) := by
  induction l with
  | nil =>
    simp only [Multiset.coe_nil, Multiset.pi_zero, pi_nil, Multiset.coe_singleton,
      Multiset.singleton_inj]
    ext i hi
    simp at hi
  | cons i l ih =>
    simp [ih, Multiset.coe_bind, ← Multiset.cons_coe]
/-
**List.mem_pi** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：mem_pi {l : List ι} (fs : forall i, List (α i)) (f : forall i in l, α i) :
 (f in pi l fs) ↔ (forall i (hi : i in l), f i hi in fs i)
参数：fs : forall i, List (α i)；f : forall i in l, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.pi_coe`：∀ {ι : Type u_1} [inst : DecidableEq ι] {α : ι → Type u
_2} (l : List ι) (fs : (i : ι) → List (α i)),   ((↑l).pi fun x => ↑(fs x)) = ↑(l
.pi f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Multiset.mem_pi`：mem_pi (m : Multiset α) (t : forall a, Multiset (β a)) 
(f : forall a in m, β a) : f in pi m t ↔ forall (a) (h : a in m), f a h in t a
-/
lemma mem_pi {l : List ι} (fs : ∀ i, List (α i)) (f : ∀ i ∈ l, α i) :
    (f ∈ pi l fs) ↔ (∀ i (hi : i ∈ l), f i hi ∈ fs i) := by
  simpa [Multiset.pi_coe] using! Multiset.mem_pi ↑l (fs ·) f

end List

