/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# Dependent-typed matrices
-/

@[expose] public section


universe u u' v w z

/-- `DMatrix m n` is the type of dependently typed matrices
whose rows are indexed by the type `m` and
whose columns are indexed by the type `n`.

In most applications `m` and `n` are finite types. -/
/-
**DMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DMatrix (m : Type u) (n : Type u') (α : m -> n -> Type v) : Type max u u' 
v
参数：m : Type u；n : Type u'；α : m -> n -> Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DMatrix m n` is the type of dependently typed matrices
whose rows are indexed by the type `m` and
whose columns are indexed by the type `n`.

In most applications `m` and `n` are finite types.
-/
def DMatrix (m : Type u) (n : Type u') (α : m → n → Type v) : Type max u u' v :=
  ∀ i j, α i j

variable {m n : Type*}
variable {α : m → n → Type v}

namespace DMatrix

section Ext

variable {M N : DMatrix m n α}

/-
**DMatrix.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：ext_iff : (forall i j, M i j = N i j) ↔ M = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

@[ext]
/-
**DMatrix.ext** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：ext : (forall i j, M i j = N i j) -> M = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DMatrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp

end Ext

/-- `M.map f` is the DMatrix obtained by applying `f` to each entry of the matrix `M`. -/
/-
**DMatrix.map** 是 Mathlib 中的一个定义，位于命名空间 `DMatrix`。
形式化陈述：map (M : DMatrix m n α) {β : m -> n -> Type w} (f : forall ⦃i j⦄, α i j ->
 β i j) : DMatrix m n β
参数：M : DMatrix m n α；f : forall ⦃i j⦄, α i j -> β i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.map f` is the DMatrix obtained by applying `f` to each entry of the matrix `M
`.
-/
def map (M : DMatrix m n α) {β : m → n → Type w} (f : ∀ ⦃i j⦄, α i j → β i j) : DMatrix m n β :=
  fun i j => f (M i j)

@[simp]
/-
**DMatrix.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：map_apply {M : DMatrix m n α} {β : m -> n -> Type w} {f : forall ⦃i j⦄, α 
i j -> β i j} {i : m} {j : n} : M.map f i j = f (M i j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply {M : DMatrix m n α} {β : m → n → Type w} {f : ∀ ⦃i j⦄, α i j → β i j} {i : m}
    {j : n} : M.map f i j = f (M i j) := rfl

@[simp]
/-
**DMatrix.map_map** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：map_map {M : DMatrix m n α} {β : m -> n -> Type w} {γ : m -> n -> Type z} 
{f : forall ⦃i j⦄, α i j -> β i j} {g : forall ⦃i j⦄, β i j -> γ i j} : (M.map f
).map g = M.map fun _ _ x => g (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map {M : DMatrix m n α} {β : m → n → Type w} {γ : m → n → Type z}
    {f : ∀ ⦃i j⦄, α i j → β i j} {g : ∀ ⦃i j⦄, β i j → γ i j} :
    (M.map f).map g = M.map fun _ _ x => g (f x) := by ext; simp

/-- The transpose of a dmatrix. -/
/-
**DMatrix.transpose** 是 Mathlib 中的一个定义，位于命名空间 `DMatrix`。
形式化陈述：{m : Type u_1} → {n : Type u_2} → {α : m → n → Type v} → DMatrix m n α → D
Matrix n m fun j i => α i j
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of a dmatrix.
-/
def transpose (M : DMatrix m n α) : DMatrix n m fun j i => α i j
  | x, y => M y x

@[inherit_doc]
scoped postfix:1024 "ᵀ" => DMatrix.transpose

/-- `DMatrix.col u` is the column matrix whose entries are given by `u`. -/
/-
**DMatrix.col** 是 Mathlib 中的一个定义，位于命名空间 `DMatrix`。
形式化陈述：{m : Type u_1} → {α : m → Type v} → ((i : m) → α i) → DMatrix m Unit fun i
 _j => α i
参数：(i : m) → α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DMatrix.col u` is the column matrix whose entries are given by `u`.
-/
def col {α : m → Type v} (w : ∀ i, α i) : DMatrix m Unit fun i _j => α i
  | x, _y => w x

/-- `DMatrix.row u` is the row matrix whose entries are given by `u`. -/
/-
**DMatrix.row** 是 Mathlib 中的一个定义，位于命名空间 `DMatrix`。
形式化陈述：{n : Type u_2} → {α : n → Type v} → ((j : n) → α j) → DMatrix Unit n fun _
i j => α j
参数：(j : n) → α j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DMatrix.row u` is the row matrix whose entries are given by `u`.
-/
def row {α : n → Type v} (v : ∀ j, α j) : DMatrix Unit n fun _i j => α j
  | _x, y => v y
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Inhabited (α i j)] : Inhabited (DMatrix m n α) :=
  inferInstanceAs <| Inhabited <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Add (α i j)] : Add (DMatrix m n α) :=
  inferInstanceAs <| Add <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α) :=
  inferInstanceAs <| AddSemigroup <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α) :=
  inferInstanceAs <| AddCommSemigroup <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Zero (α i j)] : Zero (DMatrix m n α) :=
  inferInstanceAs <| Zero <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α) :=
  inferInstanceAs <| AddMonoid <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α) :=
  inferInstanceAs <| AddCommMonoid <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Neg (α i j)] : Neg (DMatrix m n α) :=
  inferInstanceAs <| Neg <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Sub (α i j)] : Sub (DMatrix m n α) :=
  inferInstanceAs <| Sub <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddGroup (α i j)] : AddGroup (DMatrix m n α) :=
  inferInstanceAs <| AddGroup <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α) :=
  inferInstanceAs <| AddCommGroup <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Unique (α i j)] : Unique (DMatrix m n α) :=
  inferInstanceAs <| Unique <| ∀ i j, α i j
/-
**DMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α) :=
  inferInstanceAs <| Subsingleton <| ∀ i j, α i j

@[simp]
/-
**DMatrix.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：zero_apply [forall i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0
参数：α i j；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0 := rfl

@[simp]
/-
**DMatrix.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：neg_apply [forall i j, Neg (α i j)] (M : DMatrix m n α) (i j) : (-M) i j =
 -M i j
参数：α i j；M : DMatrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply [∀ i j, Neg (α i j)] (M : DMatrix m n α) (i j) : (-M) i j = -M i j := rfl

@[simp]
/-
**DMatrix.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：add_apply [forall i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) 
i j = M i j + N i j
参数：α i j；M N : DMatrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl

@[simp]
/-
**DMatrix.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：sub_apply [forall i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) 
i j = M i j - N i j
参数：α i j；M N : DMatrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply [∀ i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl

@[simp]
/-
**DMatrix.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：map_zero [forall i j, Zero (α i j)] {β : m -> n -> Type w} [forall i j, Ze
ro (β i j)] {f : forall ⦃i j⦄, α i j -> β i j} (h : forall i j, f (0 : α i j) = 
0) : (0 : DMatrix m n α).map f = 0
参数：α i j；β i j；h : forall i j, f (0 : α i j) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)]
    {f : ∀ ⦃i j⦄, α i j → β i j} (h : ∀ i j, f (0 : α i j) = 0) :
    (0 : DMatrix m n α).map f = 0 := by ext; simp [h]
/-
**DMatrix.map_add** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：map_add [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w} [forall i j
, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) (M N : DMatrix m n α) :
 ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => 
@f i j
参数：α i j；β i j；f : forall ⦃i j⦄, α i j ->+ β i j；M N : DMatrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add [∀ i j, AddMonoid (α i j)] {β : m → n → Type w} [∀ i j, AddMonoid (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j := by
  ext; simp
/-
**DMatrix.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `DMatrix`。
形式化陈述：map_sub [forall i j, AddGroup (α i j)] {β : m -> n -> Type w} [forall i j,
 AddGroup (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) (M N : DMatrix m n α) : (
(M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f
 i j
参数：α i j；β i j；f : forall ⦃i j⦄, α i j ->+ β i j；M N : DMatrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_sub [∀ i j, AddGroup (α i j)] {β : m → n → Type w} [∀ i j, AddGroup (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j := by
  ext; simp
/-
**DMatrix.subsingleton_of_empty_left** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
形式化陈述：subsingleton_of_empty_left [IsEmpty m] : Subsingleton (DMatrix m n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩
/-
**DMatrix.subsingleton_of_empty_right** 是 Mathlib 中的一个实例，位于命名空间 `DMatrix`。
形式化陈述：subsingleton_of_empty_right [IsEmpty n] : Subsingleton (DMatrix m n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by ext i j; exact isEmptyElim j⟩

end DMatrix

/-- The `AddMonoidHom` between spaces of dependently typed matrices
induced by an `AddMonoidHom` between their coefficients. -/
/-
**AddMonoidHom.mapDMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.mapDMatrix [forall i j, AddMonoid (α i j)] {β : m -> n -> Typ
e w} [forall i j, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) : DMatr
ix m n α ->+ DMatrix m n β where toFun M
参数：α i j；β i j；f : forall ⦃i j⦄, α i j ->+ β i j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DMatrix.map_add`：map_add [forall i j, AddMonoid (α i j)] {β : m -> n -> 
Type w} [forall i j, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) (M N
 : DM…

--- 原说明 ---
The `AddMonoidHom` between spaces of dependently typed matrices
induced by an `AddMonoidHom` between their coefficients.
-/
def AddMonoidHom.mapDMatrix [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) : DMatrix m n α →+ DMatrix m n β where
  toFun M := M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f

@[simp]
/-
**AddMonoidHom.mapDMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.mapDMatrix_apply [forall i j, AddMonoid (α i j)] {β : m -> n 
-> Type w} [forall i j, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) (
M : DMatrix m n α) : AddMonoidHom.mapDMatrix f M = M.map fun i j => @f i j
参数：α i j；β i j；f : forall ⦃i j⦄, α i j ->+ β i j；M : DMatrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoidHom.mapDMatrix_apply [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) (M : DMatrix m n α) :
    AddMonoidHom.mapDMatrix f M = M.map fun i j => @f i j := rfl
