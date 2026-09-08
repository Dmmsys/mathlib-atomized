/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/

@[expose] public section


/-- A member of `Semiquot α` is classically a nonempty `Set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
/-
**Semiquot** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A member of `Semiquot α` is classically a nonempty `Set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions.
-/
structure Semiquot (α : Type*) where mk' ::
  /-- Set containing some element of `α` -/
  s : Set α
  /-- Assertion of non-emptiness via `Trunc` -/
  val : Trunc s

namespace Semiquot

variable {α : Type*} {β : Type*}

/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Semiquot α) :=
  ⟨fun q a => a ∈ q.s⟩

/-- Construct a `Semiquot α` from `h : a ∈ s` where `s : Set α`. -/
/-
**Semiquot.mk** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：mk {a : α} {s : Set α} (h : a in s) : Semiquot α
参数：h : a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Semiquot α` from `h : a ∈ s` where `s : Set α`.
-/
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩
/-
**Semiquot.ext_s** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.helim`：∀ {α β : Sort u} [h₁ : Subsingleton α], α = β → ∀ (a
 : α) (b : β), a ≍ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s := by
  refine ⟨congr_arg _, fun h => ?_⟩
  obtain ⟨_, v₁⟩ := q₁; obtain ⟨_, v₂⟩ := q₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂
/-
**Semiquot.ext** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ forall a, a in q₁ ↔ a in q₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Semiquot.ext_s`：ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff
/-
**Semiquot.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：exists_mem (q : Semiquot α) : exists a, a in q
参数：q : Semiquot α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.exists_rep`：exists_rep (q : Trunc α) : exists a : α, mk a = q
-/
theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩
/-
**Semiquot.eq_mk_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：eq_mk_of_mem {q : Semiquot α} {a : α} (h : a in q) : q = @mk _ a q.1 h
参数：h : a in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semiquot.ext_s`：ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s
-/
theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl
/-
**Semiquot.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：nonempty (q : Semiquot α) : q.s.Nonempty
参数：q : Semiquot α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiquot.exists_mem`：exists_mem (q : Semiquot α) : exists a, a in q
-/
theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem

/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
/-
**Semiquot.pure** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：{α : Type u_1} → α → Semiquot α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
`pure a` is `a` reinterpreted as an unspecified element of `{a}`.
-/
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)

@[simp]
/-
**Semiquot.mem_pure'** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_pure' {a b : α} : a in Semiquot.pure b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_pure' {a b : α} : a ∈ Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff

/-- Replace `s` in a `Semiquot` with a superset. -/
/-
**Semiquot.blur'** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：blur' (q : Semiquot α) {s : Set α} (h : q.s subseteq s) : Semiquot α
参数：q : Semiquot α；h : q.s subseteq s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace `s` in a `Semiquot` with a superset.
-/
def blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩

/-- Replace `s` in a `q : Semiquot α` with a union `s ∪ q.s` -/
/-
**Semiquot.blur** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：blur (s : Set α) (q : Semiquot α) : Semiquot α
参数：s : Set α；q : Semiquot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace `s` in a `q : Semiquot α` with a union `s ∪ q.s`
-/
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (s.subset_union_right (t := q.s))
/-
**Semiquot.blur_eq_blur'** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s subseteq s) : blur s q
 = blur' q h
参数：q : Semiquot α；s : Set α；h : q.s subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
-/
theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s ⊆ s) : blur s q = blur' q h := by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h

@[simp]
/-
**Semiquot.mem_blur'** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_blur' (q : Semiquot α) {s : Set α} (h : q.s subseteq s) {a : α} : a in
 blur' q h ↔ a in s
参数：q : Semiquot α；h : q.s subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) {a : α} : a ∈ blur' q h ↔ a ∈ s :=
  Iff.rfl

/-- Convert a `Trunc α` to a `Semiquot α`. -/
/-
**Semiquot.ofTrunc** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：ofTrunc (q : Trunc α) : Semiquot α
参数：q : Trunc α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Convert a `Trunc α` to a `Semiquot α`.
-/
def ofTrunc (q : Trunc α) : Semiquot α :=
  ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩

/-- Convert a `Semiquot α` to a `Trunc α`. -/
/-
**Semiquot.toTrunc** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：toTrunc (q : Semiquot α) : Trunc α
参数：q : Semiquot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Semiquot α` to a `Trunc α`.
-/
def toTrunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val

/-- If `f` is a constant on `q.s`, then `q.liftOn f` is the value of `f`
at any point of `q`. -/
/-
**Semiquot.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：liftOn (q : Semiquot α) (f : α -> β) (h : forall a in q, forall b in q, f 
a = f b) : β
参数：q : Semiquot α；f : α -> β；h : forall a in q, forall b in q, f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a constant on `q.s`, then `q.liftOn f` is the value of `f`
at any point of `q`.
-/
def liftOn (q : Semiquot α) (f : α → β) (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2
/-
**Semiquot.liftOn_ofMem** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：liftOn_ofMem (q : Semiquot α) (f : α -> β) (h : forall a in q, forall b in
 q, f a = f b) (a : α) (aq : a in q) : liftOn q f h = f a
参数：q : Semiquot α；f : α -> β；h : forall a in q, forall b in q, f a = f b；a : α；a
q : a in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semiquot.eq_mk_of_mem`：eq_mk_of_mem {q : Semiquot α} {a : α} (h : a in q
) : q = @mk _ a q.1 h
-/
theorem liftOn_ofMem (q : Semiquot α) (f : α → β)
    (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) (a : α) (aq : a ∈ q) : liftOn q f h = f a := by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl

/-- Apply a function to the unknown value stored in a `Semiquot α`. -/
/-
**Semiquot.map** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：map (f : α -> β) (q : Semiquot α) : Semiquot β
参数：f : α -> β；q : Semiquot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a function to the unknown value stored in a `Semiquot α`.
-/
def map (f : α → β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩

@[simp]
/-
**Semiquot.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_map (f : α -> β) (q : Semiquot α) (b : β) : b in map f q ↔ exists a, a
 in q ∧ f a = b
参数：f : α -> β；q : Semiquot α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_map (f : α → β) (q : Semiquot α) (b : β) : b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b :=
  Set.mem_image _ _ _

/-- Apply a function returning a `Semiquot` to a `Semiquot`. -/
/-
**Semiquot.bind** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：bind (q : Semiquot α) (f : α -> Semiquot β) : Semiquot β
参数：q : Semiquot α；f : α -> Semiquot β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a function returning a `Semiquot` to a `Semiquot`.
-/
def bind (q : Semiquot α) (f : α → Semiquot β) : Semiquot β :=
  ⟨⋃ a ∈ q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩

@[simp]
/-
**Semiquot.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_bind (q : Semiquot α) (f : α -> Semiquot β) (b : β) : b in bind q f ↔ 
exists a in q, b in f a
参数：q : Semiquot α；f : α -> Semiquot β；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem mem_bind (q : Semiquot α) (f : α → Semiquot β) (b : β) :
    b ∈ bind q f ↔ ∃ a ∈ q, b ∈ f a := by simp_rw [← exists_prop]; exact Set.mem_iUnion₂
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad Semiquot where
  pure := @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

@[simp]
/-
**Semiquot.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：map_def {β} : ((· <$> ·) : (α -> β) -> Semiquot α -> Semiquot β) = map
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_def {β} : ((· <$> ·) : (α → β) → Semiquot α → Semiquot β) = map :=
  rfl

@[simp]
/-
**Semiquot.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：bind_def {β} : ((· >>= ·) : Semiquot α -> (α -> Semiquot β) -> Semiquot β)
 = bind
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def {β} : ((· >>= ·) : Semiquot α → (α → Semiquot β) → Semiquot β) = bind :=
  rfl

@[simp]
/-
**Semiquot.mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_pure {a b : α} : a in (pure b : Semiquot α) ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_pure {a b : α} : a ∈ (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff
/-
**Semiquot.mem_pure_self** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_pure_self (a : α) : a in (pure a : Semiquot α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem mem_pure_self (a : α) : a ∈ (pure a : Semiquot α) :=
  Set.mem_singleton a

@[simp]
/-
**Semiquot.pure_inj** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Semiquot.ext_s`：ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
-/
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Semiquot := LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
    ext.2 <| by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ext.2 <| by simp)
  (bind_pure_comp := fun {α β} f s => ext.2 <| by simp [eq_comm])
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Semiquot α) :=
  ⟨fun s t => ∀ ⦃x⦄, x ∈ s → x ∈ t⟩
/-
**Semiquot.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
形式化陈述：partialOrder : PartialOrder (Semiquot α) where le_refl _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder (Semiquot α) where
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }

@[simp]
/-
**Semiquot.pure_le** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：pure_le {a : α} {s : Semiquot α} : pure a <= s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem pure_le {a : α} {s : Semiquot α} : pure a ≤ s ↔ a ∈ s :=
  Set.singleton_subset_iff

/-- Assert that a `Semiquot` contains only one possible value. -/
/-
**Semiquot.IsPure** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：IsPure (q : Semiquot α) : Prop
参数：q : Semiquot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that a `Semiquot` contains only one possible value.
-/
def IsPure (q : Semiquot α) : Prop :=
  ∀ a ∈ q, ∀ b ∈ q, a = b

/-- Extract the value from an `IsPure` semiquotient. -/
/-
**Semiquot.get** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：get (q : Semiquot α) (h : q.IsPure) : α
参数：q : Semiquot α；h : q.IsPure。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the value from an `IsPure` semiquotient.
-/
def get (q : Semiquot α) (h : q.IsPure) : α :=
  liftOn q id h

set_option backward.isDefEq.respectTransparency false in
/-
**Semiquot.get_mem** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：get_mem {q : Semiquot α} (p) : get q p in q
参数：p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiquot.exists_mem`：exists_mem (q : Semiquot α) : exists a, a in q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semiquot.liftOn_ofMem`：liftOn_ofMem (q : Semiquot α) (f : α -> β) (h : f
orall a in q, forall b in q, f a = f b) (a : α) (aq : a in q) : liftOn q f h = f
 a
-/
theorem get_mem {q : Semiquot α} (p) : get q p ∈ q := by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h
/-
**Semiquot.eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：eq_pure {q : Semiquot α} (p) : q = pure (get q p)
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semiquot.ext`：ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ forall a, a in q₁ ↔ a
 in q₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semiquot.get_mem`：get_mem {q : Semiquot α} (p) : get q p in q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_pure {q : Semiquot α} (p) : q = pure (get q p) :=
  ext.2 fun a => by simpa using ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩

@[simp]
/-
**Semiquot.pure_isPure** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：∀ {α : Type u_1} (a : α), (pure a).IsPure
参数：a : α；pure a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Semiquot.mem_pure`：mem_pure {a b : α} : a in (pure b : Semiquot α) ↔ a =
 b
-/
theorem pure_isPure (a : α) : IsPure (pure a)
  | b, ab, c, ac => by
    rw [mem_pure] at ab ac
    rwa [← ac] at ab
/-
**Semiquot.isPure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：isPure_iff {s : Semiquot α} : IsPure s ↔ exists a, s = pure a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiquot.eq_pure`：eq_pure {q : Semiquot α} (p) : q = pure (get q p)
· 使用定理 `Semiquot.pure_isPure`：∀ {α : Type u_1} (a : α), (pure a).IsPure
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPure_iff {s : Semiquot α} : IsPure s ↔ ∃ a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩
/-
**Semiquot.IsPure.mono** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot.IsPure`。
形式化陈述：∀ {α : Type u_1} {s t : Semiquot α}, s ≤ t → t.IsPure → s.IsPure
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPure.mono {s t : Semiquot α} (st : s ≤ t) (h : IsPure t) : IsPure s
  | _, as, _, bs => h _ (st as) _ (st bs)
/-
**Semiquot.IsPure.min** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot.IsPure`。
形式化陈述：∀ {α : Type u_1} {s t : Semiquot α}, t.IsPure → (s ≤ t ↔ s = t)
参数：s ≤ t ↔ s = t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semiquot.eq_pure`：eq_pure {q : Semiquot α} (p) : q = pure (get q p)
· 使用定理 `Semiquot.IsPure.mono`：∀ {α : Type u_1} {s t : Semiquot α}, s ≤ t → t.IsP
ure → s.IsPure
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Semiquot.get_mem`：get_mem {q : Semiquot α} (p) : get q p in q
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem IsPure.min {s t : Semiquot α} (h : IsPure t) : s ≤ t ↔ s = t :=
  ⟨fun st =>
    le_antisymm st <| by
      rw [eq_pure h, eq_pure (h.mono st)]; simpa using h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩
/-
**Semiquot.isPure_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：∀ {α : Type u_1} [Subsingleton α] (q : Semiquot α), q.IsPure
参数：q : Semiquot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isPure_of_subsingleton [Subsingleton α] (q : Semiquot α) : IsPure q
  | _, _, _, _ => Subsingleton.elim _ _

/-- `univ : Semiquot α` represents an unspecified element of `univ : Set α`. -/
/-
**Semiquot.univ** 是 Mathlib 中的一个定义，位于命名空间 `Semiquot`。
形式化陈述：univ [Inhabited α] : Semiquot α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`univ : Semiquot α` represents an unspecified element of `univ : Set α`.
-/
def univ [Inhabited α] : Semiquot α :=
  mk <| Set.mem_univ default
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩

@[simp]
/-
**Semiquot.mem_univ** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：mem_univ [Inhabited α] : forall a, a in @univ α _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
  @Set.mem_univ α

@[congr]
/-
**Semiquot.univ_unique** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J
参数：I J : Inhabited α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semiquot.ext`：ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ forall a, a in q₁ ↔ a
 in q₂
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2 fun a => refl (a ∈ univ)

@[simp]
/-
**Semiquot.isPure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Semiquot`。
形式化陈述：isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩
/-
**Semiquot.** 是 Mathlib 中的一个实例，位于命名空间 `Semiquot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : OrderTop (Semiquot α) where
  top := univ
  le_top _ := Set.subset_univ _

end Semiquot

