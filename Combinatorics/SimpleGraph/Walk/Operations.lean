/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte, Daniel Weber, Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Data.List.Zip

/-!
# Operations on walks

Operations on walks that produce a new walk in the same graph.

## Main definitions

* `SimpleGraph.Walk.copy`: Change the endpoints of a walk using equalities
* `SimpleGraph.Walk.append`: Concatenate two compatible walks
* `SimpleGraph.Walk.concat`: Concatenate an edge to the end of a walk
* `SimpleGraph.Walk.reverse`: Reverse a walk
* `SimpleGraph.Walk.drop`: Remove the first `n` darts of a walk
* `SimpleGraph.Walk.take`: Take the first `n` darts of a walk
* `SimpleGraph.Walk.tail`: Remove the first dart of a walk
* `SimpleGraph.Walk.dropLast`: Remove the last dart of a walk

## Tags
walks
-/

@[expose] public section

open Function

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
/-
**SimpleGraph.Walk.copy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v u' v' : V} → G.Walk u v → u = u'
 → v = v' → G.Walk u' v'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to
-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way
 to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculatio
ns can
occur within the "copy context."
-/
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p

@[simp]
/-
**SimpleGraph.Walk.copy_rfl_rfl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl

@[simp]
/-
**SimpleGraph.Walk.copy_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：copy_copy {u v u' v' u'' v''} (p : G.Walk u v) (hu : u = u') (hv : v = v')
 (hu' : u' = u'') (hv' : v' = v'') : (p.copy hu hv).copy hu' hv' = p.copy (hu.tr
ans hu') (hv.trans hv')
参数：p : G.Walk u v；hu : u = u'；hv : v = v'；hu' : u' = u''；hv' : v' = v''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.copy_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = nil
参数：hu : u = u'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = nil := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.copy_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw
 : w = w') : (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw)
参数：h : G.Adj u v；p : G.Walk v w；hu : u = u'；hw : w = w'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.cons_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (
hw : w' = w) : cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw
参数：h : G.Adj u v；p : G.Walk v' w'；hv : v' = v；hw : w' = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

/-- The concatenation of two compatible walks. -/
@[trans]
/-
**SimpleGraph.Walk.append** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v w : V} → G.Walk u v → G.Walk v w
 → G.Walk u w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concatenation of two compatible walks.
-/
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- The reversed version of `SimpleGraph.Walk.cons`, concatenating an edge to
the end of a walk. -/
/-
**SimpleGraph.Walk.concat** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w
参数：p : G.Walk u v；h : G.Adj v w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reversed version of `SimpleGraph.Walk.cons`, concatenating an edge to
the end of a walk.
-/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)
/-
**SimpleGraph.Walk.concat_eq_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : p.concat h
 = p.append (cons h nil)
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) := rfl

/-- The concatenation of the reverse of the first walk with the second walk. -/
/-
**SimpleGraph.Walk.reverseAux** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v w : V} → G.Walk u v → G.Walk u w
 → G.Walk v w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concatenation of the reverse of the first walk with the second walk.
-/
protected def reverseAux {u v w : V} : G.Walk u v → G.Walk u w → G.Walk v w
  | nil, q => q
  | cons h p, q => p.reverseAux <| cons h.symm q

/-- The walk in reverse. -/
@[symm]
/-
**SimpleGraph.Walk.reverse** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse {u v : V} (w : G.Walk u v) : G.Walk v u
参数：w : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk in reverse.
-/
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil

@[simp]
/-
**SimpleGraph.Walk.cons_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x
) : (cons h p).append q = cons h (p.append q)
参数：h : G.Adj u v；p : G.Walk v w；q : G.Walk w x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp]
/-
**SimpleGraph.Walk.cons_nil_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h nil
).append p = cons h p
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl

@[simp]
/-
**SimpleGraph.Walk.nil_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_append {u v : V} (p : G.Walk u v) : nil.append p = p
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.append_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：append_nil {u v : V} (p : G.Walk u v) : p.append nil = p
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p <;> simp [*]
/-
**SimpleGraph.Walk.append_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w
 x) : p.append (q.append r) = (p.append q).append r
参数：p : G.Walk u v；q : G.Walk v w；r : G.Walk w x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.append_copy_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w) (hu : 
u = u') (hv : v = v') (hw : w = w') : (p.copy hu hv).append (q.copy hv hw) = (p.
append q).copy hu hw
参数：p : G.Walk u v；q : G.Walk v w；hu : u = u'；hv : v = v'；hw : w = w'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.concat_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil := rfl

@[simp]
/-
**SimpleGraph.Walk.concat_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x
) : (cons h p).concat h' = cons h (p.concat h')
参数：h : G.Adj u v；p : G.Walk v w；h' : G.Adj w x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x) :
    (cons h p).concat h' = cons h (p.concat h') := rfl
/-
**SimpleGraph.Walk.append_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w
 x) : p.append (q.concat h) = (p.append q).concat h
参数：p : G.Walk u v；q : G.Walk v w；h : G.Adj w x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.append_assoc`：append_assoc {u v w x : V} (p : G.Walk u 
v) (q : G.Walk v w) (r : G.Walk w x) : p.append (q.append r) = (p.append q).appe
nd r
-/
theorem append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x) :
    p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _
/-
**SimpleGraph.Walk.concat_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w
 x) : (p.concat h).append q = p.append (cons h q)
参数：p : G.Walk u v；h : G.Adj v w；q : G.Walk w x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.concat_eq_append`：concat_eq_append {u v w : V} (p : G.W
alk u v) (h : G.Adj v w) : p.concat h = p.append (cons h nil)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.append_assoc`：append_assoc {u v w x : V} (p : G.Walk u 
v) (q : G.Walk v w) (r : G.Walk w x) : p.append (q.append r) = (p.append q).appe
nd r
· 使用定理 `SimpleGraph.Walk.cons_nil_append`：cons_nil_append {u v w : V} (h : G.Adj
 u v) (p : G.Walk v w) : (cons h nil).append p = cons h p
-/
theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append, ← append_assoc, cons_nil_append]

/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
/-
**SimpleGraph.Walk.exists_cons_eq_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：exists_cons_eq_concat {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : exist
s (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h'
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.concat_cons`：concat_cons {u v w x : V} (h : G.Adj u v) 
(p : G.Walk v w) (h' : G.Adj w x) : (cons h p).concat h' = cons h (p.concat h')
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A non-trivial `cons` walk is representable as a `concat` walk.
-/
theorem exists_cons_eq_concat {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    ∃ (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h' := by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    exact ⟨y, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
/-
**SimpleGraph.Walk.exists_concat_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (h : G.Adj
 v w),   ∃ x, ∃ (h' : G.Adj u x), ∃ q, p.concat h = SimpleGraph.Walk.cons h' q
参数：p : G.Walk u v；h : G.Adj v w；h' : G.Adj u x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.concat_cons`：concat_cons {u v w x : V} (h : G.Adj u v) 
(p : G.Walk v w) (h' : G.Adj w x) : (cons h p).concat h' = cons h (p.concat h')

--- 原说明 ---
A non-trivial `concat` walk is representable as a `cons` walk.
-/
theorem exists_concat_eq_cons {u v w : V} :
    ∀ (p : G.Walk u v) (h : G.Adj v w),
      ∃ (x : V) (h' : G.Adj u x) (q : G.Walk x w), p.concat h = cons h' q
  | nil, h => ⟨_, h, nil, rfl⟩
  | cons h' p, h => ⟨_, h', Walk.concat p h, concat_cons _ _ _⟩

@[simp]
/-
**SimpleGraph.Walk.reverse_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil := rfl
/-
**SimpleGraph.Walk.reverse_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons 
h.symm nil
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons h.symm nil :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.reverse_toWalk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_toWalk {u v : V} (h : G.Adj u v) : h.toWalk.reverse = h.symm.toWal
k
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_toWalk {u v : V} (h : G.Adj u v) : h.toWalk.reverse = h.symm.toWalk := rfl

@[simp]
/-
**SimpleGraph.Walk.cons_reverseAux** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj
 w u) : (cons h p).reverseAux q = p.reverseAux (cons h.symm q)
参数：p : G.Walk u v；q : G.Walk w x；h : G.Adj w u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons h.symm q) := rfl

@[simp]
/-
**SimpleGraph.Walk.append_reverseAux** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w x : V} (p : G.Walk u v) (q : G.W
alk v w) (r : G.Walk u x),   (p.append q).reverseAux r = q.reverseAux (p.reverse
Aux r)
参数：p : G.Walk u v；q : G.Walk v w；r : G.Walk u x；p.append q；p.reverseAux r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
protected theorem append_reverseAux {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons h.symm r)

@[simp]
/-
**SimpleGraph.Walk.reverseAux_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w x : V} (p : G.Walk u v) (q : G.W
alk u w) (r : G.Walk w x),   (p.reverseAux q).append r = p.reverseAux (q.append 
r)
参数：p : G.Walk u v；q : G.Walk u w；r : G.Walk w x；p.reverseAux q；q.append r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem reverseAux_append {u v w x : V}
    (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons h.symm q)]
/-
**SimpleGraph.Walk.reverseAux_eq_reverse_append** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q : G.Wal
k u w), p.reverseAux q = p.reverse.append q
参数：p : G.Walk u v；q : G.Walk u w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverseAux_append`：∀ {V : Type u} {G : SimpleGraph V} {
u v w x : V} (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x),   (p.reverseAux
 q).append r = p.reverse…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem reverseAux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]

@[simp]
/-
**SimpleGraph.Walk.reverse_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).rev
erse = p.reverse.append (cons h.symm nil)
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverseAux_append`：∀ {V : Type u} {G : SimpleGraph V} {
u v w x : V} (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x),   (p.reverseAux
 q).append r = p.reverse…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons h.symm nil) := by simp [reverse]

@[simp]
/-
**SimpleGraph.Walk.reverse_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p
.copy hu hv).reverse = p.reverse.copy hv hu
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.reverse_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q
).reverse = q.reverse.append p.reverse
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_reverseAux`：∀ {V : Type u} {G : SimpleGraph V} {
u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x),   (p.append q).
reverseAux r = q.reverse…
· 使用定理 `SimpleGraph.Walk.reverseAux_append`：∀ {V : Type u} {G : SimpleGraph V} {
u v w x : V} (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x),   (p.reverseAux
 q).append r = p.reverse…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]

@[simp]
/-
**SimpleGraph.Walk.reverse_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : (p.concat h)
.reverse = cons h.symm p.reverse
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_append`：reverse_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).reverse = q.reverse.append p.reverse
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).reverse = cons h.symm p.reverse := by simp [concat_eq_append]

@[simp]
/-
**SimpleGraph.Walk.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_reverse {u v : V} (p : G.Walk u v) : p.reverse.reverse = p
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.reverse_append`：reverse_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).reverse = q.reverse.append p.reverse
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_reverse {u v : V} (p : G.Walk u v) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
/-
**SimpleGraph.Walk.reverse_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：reverse_surjective {u v : V} : Function.Surjective (reverse : G.Walk u v -
> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
-/
theorem reverse_surjective {u v : V} : Function.Surjective (reverse : G.Walk u v → _) :=
  RightInverse.surjective reverse_reverse
/-
**SimpleGraph.Walk.reverse_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：reverse_injective {u v : V} : Function.Injective (reverse : G.Walk u v -> 
_)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
-/
theorem reverse_injective {u v : V} : Function.Injective (reverse : G.Walk u v → _) :=
  RightInverse.injective reverse_reverse
/-
**SimpleGraph.Walk.reverse_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：reverse_bijective {u v : V} : Function.Bijective (reverse : G.Walk u v -> 
_)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.reverse_injective`：reverse_injective {u v : V} : Functi
on.Injective (reverse : G.Walk u v -> _)
· 使用定理 `SimpleGraph.Walk.reverse_surjective`：reverse_surjective {u v : V} : Func
tion.Surjective (reverse : G.Walk u v -> _)
-/
theorem reverse_bijective {u v : V} : Function.Bijective (reverse : G.Walk u v → _) :=
  ⟨reverse_injective, reverse_surjective⟩

@[simp]
/-
**SimpleGraph.Walk.length_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.
copy hu hv).length = p.length
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.length_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q)
.length = p.length + q.length
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]
/-
**SimpleGraph.Walk.length_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : (p.concat h).
length = p.length + 1
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
-/
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 := length_append _ _

@[simp]
/-
**SimpleGraph.Walk.length_reverseAux** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q : G.Wal
k u w),   (p.reverseAux q).length = p.length + q.length
参数：p : G.Walk u v；q : G.Walk u w；p.reverseAux q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
-/
protected theorem length_reverseAux {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]
/-
**SimpleGraph.Walk.length_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_reverseAux`：∀ {V : Type u} {G : SimpleGraph V} {
u v w : V} (p : G.Walk u v) (q : G.Walk u w),   (p.reverseAux q).length = p.leng
th + q.length
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]
/-
**SimpleGraph.Walk.getVert_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : Nat) : (
p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.l
ength)
参数：p : G.Walk u v；q : G.Walk v w；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i <;> cases i <;> simp [*]

/-- This uses `p` instead of `q` when `i = p.length` unlike the unprimed version. -/
/-
**SimpleGraph.Walk.getVert_append'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_append' (p : G.Walk u v) (q : G.Walk v w) (i : Nat) : (p.append q)
.getVert i = if i <= p.length then p.getVert i else q.getVert (i - p.length)
参数：p : G.Walk u v；q : G.Walk v w；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
This uses `p` instead of `q` when `i = p.length` unlike the unprimed version.
-/
theorem getVert_append' (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i ≤ p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i <;> cases i <;> simp [*]
/-
**SimpleGraph.Walk.getVert_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_reverse {u v : V} (p : G.Walk u v) (i : Nat) : p.reverse.getVert i
 = p.getVert (p.length - i)
参数：p : G.Walk u v；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.getVert_append`：getVert_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) (i : Nat) : (p.append q).getVert i = if i < p.length then 
p.getVert i else q.ge…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.succ_sub`：∀ {m n : ℕ}, n ≤ m → m.succ - n = (m - n).succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `eq_or_gt_of_not_lt`：eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_add_of_sub_eq`：∀ {a b c : ℕ}, b ≤ a → a - b = c → a = c + b
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem getVert_reverse {u v : V} (p : G.Walk u v) (i : ℕ) :
    p.reverse.getVert i = p.getVert (p.length - i) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi => simp [Nat.succ_sub hi.le]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp

section ConcatRec

variable {motive : ∀ u v : V, G.Walk u v → Sort*} (Hnil : ∀ {u : V}, motive u u nil)
  (Hconcat : ∀ {u v w : V} (p : G.Walk u v) (h : G.Adj v w), motive u v p → motive u w (p.concat h))

/-- Auxiliary definition for `SimpleGraph.Walk.concatRec` -/
/-
**SimpleGraph.Walk.concatRecAux** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     {motive : (u v : V) → G.Walk u 
v → Sort u_1} →       ({u : V} → motive u u SimpleGraph.Walk.nil) →         ({u 
v w : V} → (p : G.Walk u v) → (h : G.Adj v w) → motive u v p → motive u w (p.con
cat h)) →           {u v : V} → (p : G.Walk u v) → motive v u p.reverse
参数：u v : V；{u : V} → motive u u SimpleGraph.Walk.nil；{u v w : V} → (p : G.Walk u
 v) → (h : G.Adj v w) → motive u v p → motive u w (p.concat h)；p : G.Walk u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SimpleGraph.Walk.concatRec`
-/
def concatRecAux {u v : V} : (p : G.Walk u v) → motive v u p.reverse
  | nil => Hnil
  | cons h p => reverse_cons h p ▸ Hconcat p.reverse h.symm (concatRecAux p)

/-- Recursor on walks by inducting on `SimpleGraph.Walk.concat`.

This is inducting from the opposite end of the walk compared
to `SimpleGraph.Walk.rec`, which inducts on `SimpleGraph.Walk.cons`. -/
@[elab_as_elim]
/-
**SimpleGraph.Walk.concatRec** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concatRec {u v : V} (p : G.Walk u v) : motive u v p
参数：p : G.Walk u v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p

--- 原说明 ---
Recursor on walks by inducting on `SimpleGraph.Walk.concat`.

This is inducting from the opposite end of the walk compared
to `SimpleGraph.Walk.rec`, which inducts on `SimpleGraph.Walk.cons`.
-/
def concatRec {u v : V} (p : G.Walk u v) : motive u v p :=
  reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse

@[simp]
/-
**SimpleGraph.Walk.concatRec_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concatRec_nil (u : V) : @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.
Walk u u) = Hnil
参数：u : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem concatRec_nil (u : V) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.Walk u u) = Hnil := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.concatRec_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：concatRec_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : @concatRec
 _ _ motive @Hnil @Hconcat _ _ (p.concat h) = Hconcat p h (concatRec @Hnil @Hcon
cat p)
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
· 使用定理 `rec_heq_of_heq`：rec_heq_of_heq {α β : Sort _} {a b : α} {C : α -> Sort*}
 {x : C a} {y : β} (e : a = b) (h : x ≍ y) : e ▸ x ≍ y
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_concat`：reverse_concat {u v w : V} (p : G.Walk 
u v) (h : G.Adj v w) : (p.concat h).reverse = cons h.symm p.reverse
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Walk.concatRecAux.eq_2`：∀ {V : Type u} {G : SimpleGraph V} {
motive : (u v : V) → G.Walk u v → Sort u_1}   (Hnil : {u : V} → motive u u Simpl
eGraph.Walk.nil)   (Hcon…
· 使用定理 `eqRec_heq_iff`：∀ {β : Sort v} {α : Sort u} {a : α} {motive : (b : α) → a
 = b → Sort v} {b : α} {refl : motive a ⋯} {h : a = b} {c : β},   h ▸ refl ≍ c ↔
 re…
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
theorem concatRec_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (p.concat h) =
      Hconcat p h (concatRec @Hnil @Hconcat p) := by
  simp only [concatRec]
  apply eq_of_heq (rec_heq_of_heq _ _)
  trans concatRecAux @Hnil @Hconcat (cons h.symm p.reverse)
  · congr
    simp
  · rw [concatRecAux, eqRec_heq_iff]
    congr <;> simp

end ConcatRec

/-
**SimpleGraph.Walk.concat_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h != n
il
参数：p : G.Walk u v；h : G.Adj v u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h ≠ nil := by
  cases p <;> simp [concat]
/-
**SimpleGraph.Walk.concat_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_inj {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u 
v'} {h' : G.Adj v' w} (he : p.concat h = p'.concat h') : exists hv : v = v', p.c
opy rfl hv = p'
参数：he : p.concat h = p'.concat h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.cons.injEq`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V} (h : G.Adj u v) (p : G.Walk v w) (v_1 : V) (h_1 : G.Adj u v_1)   (p_1 : G.Wa
lk v_1 w), (Simpl…
· 使用定理 `SimpleGraph.Walk.concat_ne_nil`：concat_ne_nil {u v : V} (p : G.Walk u v)
 (h : G.Adj v u) : p.concat h != nil
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.concat_cons`：concat_cons {u v w x : V} (h : G.Adj u v) 
(p : G.Walk v w) (h' : G.Adj w x) : (cons h p).concat h' = cons h (p.concat h')
-/
theorem concat_inj {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
    {h' : G.Adj v' w} (he : p.concat h = p'.concat h') : ∃ hv : v = v', p.copy rfl hv = p' := by
  induction p with
  | nil =>
    cases p'
    · exact ⟨rfl, rfl⟩
    · simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he).symm).elim
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · simp only [concat_nil, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he)).elim
    · rw [concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih (heq_iff_eq.mp he)
      exact ⟨rfl, rfl⟩

@[simp]
/-
**SimpleGraph.Walk.support_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_concat (p : G.Walk u v) (h : G.Adj v w) : (p.concat h).support = p
.support ++ [w]
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem support_concat (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).support = p.support ++ [w] := by
  induction p <;> simp [*, concat_nil]

@[simp]
/-
**SimpleGraph.Walk.support_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p
.copy hu hv).support = p.support
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.support_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append 
p').support = p.support ++ p'.support.tail
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support ++ p'.support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.support_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support
.reverse
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]
/-
**SimpleGraph.Walk.support_append_eq_support_dropLast_append** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_append_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p'
 : G.Walk v w) : (p.append p').support = p.support.dropLast ++ p'.support
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.dropLast_cons_of_ne_nil`：∀ {α : Type u} {x : α} {l : List α}, l ≠ [
] → (x :: l).dropLast = x :: l.dropLast
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_append_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support.dropLast ++ p'.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]
/-
**SimpleGraph.Walk.tail_support_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.ap
pend p').support.tail = p.support.tail ++ p'.support.tail
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `List.tail_append_of_ne_nil`：∀ {α : Type u_1} {xs ys : List α}, xs ≠ [] →
 (xs ++ ys).tail = xs.tail ++ ys
· 使用定理 `SimpleGraph.Walk.support_ne_nil`：support_ne_nil {u v : V} (p : G.Walk u 
v) : p.support != []
-/
theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil (support_ne_nil _)]

@[simp]
/-
**SimpleGraph.Walk.dropLast_support_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：dropLast_support_concat (p : G.Walk u v) : p.support.dropLast ++ [v] = p.s
upport
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.exists_cons_eq_concat`：exists_cons_eq_concat {u v w : V
} (h : G.Adj u v) (p : G.Walk v w) : exists (x : V) (q : G.Walk u x) (h' : G.Adj
 x w), cons h p = q.concat h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.support_concat`：support_concat (p : G.Walk u v) (h : G.
Adj v w) : (p.concat h).support = p.support ++ [w]
· 使用定理 `List.dropLast_append_of_ne_nil`：∀ {α : Type u} {l l' : List α}, l ≠ [] →
 (l' ++ l).dropLast = l' ++ l.dropLast
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dropLast_support_concat (p : G.Walk u v) : p.support.dropLast ++ [v] = p.support := by
  cases p with | nil => rfl | cons h p
  have ⟨_, _, _, hp⟩ := p.exists_cons_eq_concat h
  simp [hp]

@[deprecated dropLast_support_concat (since := "2026-03-16")]
/-
**SimpleGraph.Walk.support_eq_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：support_eq_concat (p : G.Walk u v) : p.support = p.support.dropLast.concat
 v
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `SimpleGraph.Walk.dropLast_support_concat`：dropLast_support_concat (p : G
.Walk u v) : p.support.dropLast ++ [v] = p.support
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_eq_concat (p : G.Walk u v) : p.support = p.support.dropLast.concat v := by
  simp
/-
**SimpleGraph.Walk.ext_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：ext_support {u v} {p q : G.Walk u v} (h : p.support = q.support) : p = q
参数：h : p.support = q.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.darts_injective`：darts_injective {u v : V} : Function.I
njective (Walk.darts : G.Walk u v -> List G.Dart)
· 使用定理 `Function.Injective.list_map`：∀ {α : Type u} {β : Type v} {f : α → β}, Fu
nction.Injective f → Function.Injective (List.map f)
· 使用定理 `SimpleGraph.Dart.toProd_injective`：∀ {V : Type u_1} {G : SimpleGraph V},
 Function.Injective SimpleGraph.Dart.toProd
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `List.rightInverse_unzip_zip`：rightInverse_unzip_zip : RightInverse (unzi
p : List (α × β) -> List α × List β) (uncurry zip)
-/
lemma ext_support {u v} {p q : G.Walk u v} (h : p.support = q.support) : p = q := by
  refine darts_injective (Dart.toProd_injective.list_map (List.rightInverse_unzip_zip.injective ?_))
  have : Prod.fst ∘ Dart.toProd = fun d : G.Dart ↦ d.fst := rfl
  have : Prod.snd ∘ Dart.toProd = fun d : G.Dart ↦ d.snd := rfl
  grind [map_fst_darts, map_snd_darts]

@[simp]
/-
**SimpleGraph.Walk.mem_tail_support_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v 
w) : t in (p.append p').support.tail ↔ t in p.support.tail ∨ t in p'.support.tai
l
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.tail_support_append`：tail_support_append {u v w : V} (p
 : G.Walk u v) (p' : G.Walk v w) : (p.append p').support.tail = p.support.tail +
+ p'.support.tail
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_append]

@[simp]
/-
**SimpleGraph.Walk.mem_support_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : 
t in (p.append p').support ↔ t in p.support ∨ t in p'.support
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support := by
  grind [mem_support_iff, mem_tail_support_append_iff, end_mem_tail_support_of_ne]
/-
**SimpleGraph.Walk.support_prefix_support_concat** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_prefix_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v
 w) : p.support <+: (p.concat hadj).support
参数：p : G.Walk u v；hadj : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_concat`：support_concat (p : G.Walk u v) (h : G.
Adj v w) : (p.concat h).support = p.support ++ [w]
-/
theorem support_prefix_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support <+: (p.concat hadj).support := by
  simp
/-
**SimpleGraph.Walk.support_subset_support_concat** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_subset_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v
 w) : p.support subseteq (p.concat hadj).support
参数：p : G.Walk u v；hadj : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_concat`：support_concat (p : G.Walk u v) (h : G.
Adj v w) : (p.concat h).support = p.support ++ [w]
-/
theorem support_subset_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support ⊆ (p.concat hadj).support := by
  simp
/-
**SimpleGraph.Walk.support_prefix_support_append** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_prefix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
 (p : G.Walk u v) (q : G.Walk v w) : p.support <+: (p.append q).support
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
-/
theorem support_prefix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support <+: (p.append q).support := by
  simp [support_append]

@[simp]
/-
**SimpleGraph.Walk.support_subset_support_append_left** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：support_subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w
 : V} (p : G.Walk u v) (q : G.Walk v w) : p.support subseteq (p.append q).suppor
t
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.support_prefix_support_append`：support_prefix_support_a
ppend {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q : G.Walk 
v w) : p.support <+: (p.append q).su…
-/
theorem support_subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support :=
  support_prefix_support_append p q |>.subset

@[deprecated (since := "2026-05-25")]
alias subset_support_append_left := support_subset_support_append_left
/-
**SimpleGraph.Walk.support_suffix_support_append** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_suffix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
 (p : G.Walk u v) (q : G.Walk v w) : q.support <:+ (p.append q).support
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append_eq_support_dropLast_append`：support_appe
nd_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (
p.append p').support = p.support.dropLast ++ p'.…
-/
theorem support_suffix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support <:+ (p.append q).support := by
  simp [support_append_eq_support_dropLast_append]

@[simp]
/-
**SimpleGraph.Walk.support_subset_support_append_right** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：support_subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v 
w : V} (p : G.Walk u v) (q : G.Walk v w) : q.support subseteq (p.append q).suppo
rt
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.support_suffix_support_append`：support_suffix_support_a
ppend {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q : G.Walk 
v w) : q.support <:+ (p.append q).su…
-/
theorem support_subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support :=
  support_suffix_support_append p q |>.subset

@[deprecated (since := "2026-05-25")]
alias subset_support_append_right := support_subset_support_append_right
/-
**SimpleGraph.Walk.coe_support_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : ((p.ap
pend p').support : Multiset V) = {u} + p.support.tail + p'.support.tail
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_add`：coe_add (s t : List α) : (s + t : Multiset α) = (s ++ 
t : List α)
· 使用定理 `SimpleGraph.Walk.coe_support`：coe_support {u v : V} (p : G.Walk u v) : (
p.support : Multiset V) = {u} + p.support.tail
-/
theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]
/-
**SimpleGraph.Walk.coe_support_append'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.W
alk v w) : ((p.append p').support : Multiset V) = p.support + p'.support - {v}
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.coe_support`：coe_support {u v : V} (p : G.Walk u v) : (
p.support : Multiset V) = {u} + p.support.tail
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} := by
  simp_rw [support_append, ← Multiset.coe_add, coe_support, add_comm ({v} : Multiset V),
    ← add_assoc, add_tsub_cancel_right]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.ofSupport_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：ofSupport_support {u v : V} (p : G.Walk u v) : ofSupport _ p.support_ne_ni
l p.isChain_adj_support = p.copy (by simp) (by simp)
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `SimpleGraph.Walk.support_ne_nil`：support_ne_nil {u v : V} (p : G.Walk u 
v) : p.support != []
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `SimpleGraph.Walk.isChain_adj_support`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} (p : G.Walk u v), List.IsChain G.Adj p.support
-/
theorem ofSupport_support {u v : V} (p : G.Walk u v) :
    ofSupport _ p.support_ne_nil p.isChain_adj_support = p.copy (by simp) (by simp) := by
  match p with
  | nil => rfl
  | cons (v := w) h .nil => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p) =>
    have := p.cons h₂ |>.ofSupport_support
    simp at this
    simp [this]

@[simp]
/-
**SimpleGraph.Walk.darts_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : (p.concat h).d
arts = p.darts.concat ⟨(v, w), h⟩
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by
  induction p <;> simp [*, concat_nil]

@[simp]
/-
**SimpleGraph.Walk.darts_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.c
opy hu hv).darts = p.darts
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).darts = p.darts := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.darts_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append p'
).darts = p.darts ++ p'.darts
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').darts = p.darts ++ p'.darts := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.darts_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_reverse {u v : V} (p : G.Walk u v) : p.reverse.darts = (p.darts.map 
Dart.symm).reverse
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.darts_append`：darts_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').darts = p.darts ++ p'.darts
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
-/
theorem darts_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.darts = (p.darts.map Dart.symm).reverse := by
  induction p <;> simp [*]
/-
**SimpleGraph.Walk.mem_darts_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} : d in p.reverse
.darts ↔ d.symm in p.darts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_reverse`：darts_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.darts = (p.darts.map Dart.symm).reverse
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} :
    d ∈ p.reverse.darts ↔ d.symm ∈ p.darts := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.ofDarts_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：ofDarts_darts {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) : ofDarts _ (darts_
eq_nil.not.mpr hp) p.isChain_dartAdj_darts = p.copy (by simp) (by simp)
参数：hp : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `SimpleGraph.Walk.isChain_dartAdj_darts`：∀ {V : Type u} {G : SimpleGraph 
V} {u v : V} (p : G.Walk u v), List.IsChain G.DartAdj p.darts
-/
theorem ofDarts_darts {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) :
    ofDarts _ (darts_eq_nil.not.mpr hp) p.isChain_dartAdj_darts = p.copy (by simp) (by simp) := by
  match p, hp with
  | nil, hp => simp at hp
  | cons (v := w) h .nil, _ => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p), _ =>
    have := p.cons h₂ |>.ofDarts_darts not_nil_cons
    simp at this
    simp [this]

@[simp]
/-
**SimpleGraph.Walk.edges_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : (p.concat h).e
dges = p.edges.concat s(v, w)
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_concat`：darts_concat {u v w : V} (p : G.Walk u v)
 (h : G.Adj v w) : (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edges = p.edges.concat s(v, w) := by simp [edges]

@[simp]
/-
**SimpleGraph.Walk.edges_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.c
opy hu hv).edges = p.edges
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.edges_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append p'
).edges = p.edges ++ p'.edges
参数：p : G.Walk u v；p' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_append`：darts_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').darts = p.darts ++ p'.darts
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').edges = p.edges ++ p'.edges := by simp [edges]

@[simp]
/-
**SimpleGraph.Walk.edges_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.rever
se
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_reverse`：darts_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.darts = (p.darts.map Dart.symm).reverse
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `SimpleGraph.Dart.edge_comp_symm`：∀ {V : Type u_1} {G : SimpleGraph V}, S
impleGraph.Dart.edge ∘ SimpleGraph.Dart.symm = SimpleGraph.Dart.edge
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [edges]
/-
**SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk`。
形式化陈述：dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart} 
(h : d in p.darts) : d.snd in p.support
参数：p : G.Walk u v；h : d in p.darts。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
· 使用定理 `SimpleGraph.Dart.symm_toProd`：∀ {V : Type u_1} {G : SimpleGraph V} (d : 
G.Dart), d.symm.toProd = d.swap
· 使用定理 `SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts`：∀ {V : Type u} {G : 
SimpleGraph V} {u v : V} (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.toProd.1
 ∈ p.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.darts_reverse`：darts_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.darts = (p.darts.map Dart.symm).reverse
· 使用定理 `SimpleGraph.Dart.symm_symm`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.
Dart), d.symm.symm = d
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d ∈ p.darts) : d.snd ∈ p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)
/-
**SimpleGraph.Walk.fst_mem_support_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) 
in p.edges) : t in p.support
参数：p : G.Walk v w；he : s(t, u) in p.edges。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dart_edge_eq_mk'_iff'`：∀ {V : Type u_1} {G : SimpleGraph V} 
{d : G.Dart} {u v : V},   d.edge = s(u, v) ↔ d.toProd.1 = u ∧ d.toProd.2 = v ∨ d
.toProd.1 = v ∧ d.toPro…
· 使用定理 `SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts`：∀ {V : Type u} {G : 
SimpleGraph V} {u v : V} (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.toProd.1
 ∈ p.support
· 使用定理 `SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts`：dart_snd_mem_support
_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart} (h : d in p.darts) : d.snd
 in p.support
-/
theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    t ∈ p.support := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd
/-
**SimpleGraph.Walk.snd_mem_support_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) 
in p.edges) : u in p.support
参数：p : G.Walk v w；he : s(t, u) in p.edges。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    u ∈ p.support :=
  p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)
/-
**SimpleGraph.Walk.mem_support_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：mem_support_of_mem_edges {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e
 in p.edges) (hv : w in e) : w in p.support
参数：he : e in p.edges；hv : w in e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
-/
theorem mem_support_of_mem_edges {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e ∈ p.edges)
    (hv : w ∈ e) : w ∈ p.support :=
  hv.elim fun _ heq ↦ p.fst_mem_support_of_mem_edges <| heq ▸ he
/-
**SimpleGraph.Walk.edges_nodup_of_support_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nod
up) : p.edges.Nodup
参数：h : p.support.Nodup。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [support_cons, List.nodup_cons, edges_cons] at h ⊢
    exact ⟨(h.1 <| fst_mem_support_of_mem_edges p' ·), ih h.2⟩
/-
**SimpleGraph.Walk.nodup_tail_support_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：nodup_tail_support_reverse {u : V} {p : G.Walk u u} : p.reverse.support.ta
il.Nodup ↔ p.support.tail.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.nodup_tail_reverse`：nodup_tail_reverse (l : List α) (h : l[0]? = l.
getLast?) : Nodup l.reverse.tail ↔ Nodup l.tail
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem?`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {n : ℕ} (p : G.Walk u v), n ≤ p.length → some (p.getVert n) =
 p.support[n]?
· 使用定理 `List.getLast?_eq_getElem?`：∀ {α : Type u_1} {l : List α}, l.getLast? = l
[l.length - 1]?
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
-/
theorem nodup_tail_support_reverse {u : V} {p : G.Walk u u} :
    p.reverse.support.tail.Nodup ↔ p.support.tail.Nodup := by
  refine p.support_reverse ▸ p.support.nodup_tail_reverse ?_
  rw [← getVert_eq_support_getElem? _ (by lia), List.getLast?_eq_getElem?,
    ← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; lia)]
  simp

@[simp]
/-
**SimpleGraph.Walk.edgeSet_reverse** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_reverse {u v : V} (p : G.Walk u v) : p.reverse.edgeSet = p.edgeSet
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma edgeSet_reverse {u v : V} (p : G.Walk u v) : p.reverse.edgeSet = p.edgeSet := by ext; simp

@[simp]
/-
**SimpleGraph.Walk.edgeSet_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : (p.concat h)
.edgeSet = insert s(v, w) p.edgeSet
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_concat`：edges_concat {u v w : V} (p : G.Walk u v)
 (h : G.Adj v w) : (p.concat h).edges = p.edges.concat s(v, w)
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edgeSet = insert s(v, w) p.edgeSet := by ext; simp [or_comm]
/-
**SimpleGraph.Walk.edgeSet_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q
).edgeSet = p.edgeSet union q.edgeSet
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_append`：edges_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').edges = p.edges ++ p'.edges
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by ext; simp

@[simp]
/-
**SimpleGraph.Walk.edgeSet_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p
.copy hu hv).edgeSet = p.edgeSet
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_copy`：edges_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).edges = p.edges
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edgeSet = p.edgeSet := by ext; simp

@[simp]
/-
**SimpleGraph.Walk.nil_append_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_append_iff {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Ni
l ∧ q.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma nil_append_iff {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  cases p <;> cases q <;> simp
/-
**SimpleGraph.Walk.Nil.append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Nil`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w}, p.Nil → q.Nil → (p.append q).Nil
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Nil.append {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil) :
    (p.append q).Nil := by
  simp [hp, hq]

@[simp]
/-
**SimpleGraph.Walk.nil_reverse** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil := by
  cases p <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The walk obtained by removing the first `n` darts of a walk. -/
/-
**SimpleGraph.Walk.drop** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop {u v : V} (p : G.Walk u v) (n : Nat) : G.Walk (p.getVert n) v
参数：p : G.Walk u v；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk obtained by removing the first `n` darts of a walk.
-/
def drop {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]
/-
**SimpleGraph.Walk.drop_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_length (p : G.Walk u v) (n : Nat) : (p.drop n).length = p.length - n
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma drop_length (p : G.Walk u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.drop_getVert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_getVert (p : G.Walk u v) (n m : Nat) : (p.drop n).getVert m = p.getVe
rt (n + m)
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma drop_getVert (p : G.Walk u v) (n m : ℕ) : (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n <;> cases n <;> simp [*, drop, add_right_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.drop_add_heq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_add_heq (p : G.Walk u v) (n m : Nat) : p.drop (n + m) ≍ (p.drop n).dr
op m
参数：p : G.Walk u v；n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.drop.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u : V} (
n : ℕ), SimpleGraph.Walk.nil.drop n = SimpleGraph.Walk.nil
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma drop_add_heq (p : G.Walk u v) (n m : ℕ) : p.drop (n + m) ≍ (p.drop n).drop m := by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [*, drop]
/-
**SimpleGraph.Walk.drop_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_add_eq (p : G.Walk u v) (n m : Nat) : p.drop (n + m) = ((p.drop n).dr
op m).copy (drop_getVert ..) rfl
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SimpleGraph.Walk.drop_getVert`：drop_getVert (p : G.Walk u v) (n m : Nat)
 : (p.drop n).getVert m = p.getVert (n + m)
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用引理 `SimpleGraph.Walk.drop_add_heq`：drop_add_heq (p : G.Walk u v) (n m : Nat)
 : p.drop (n + m) ≍ (p.drop n).drop m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma drop_add_eq (p : G.Walk u v) (n m : ℕ) :
    p.drop (n + m) = ((p.drop n).drop m).copy (drop_getVert ..) rfl :=
  eq_of_heq <| drop_add_heq .. |>.trans <| by simp [Walk.copy]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.nil_drop_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_drop_iff (p : G.Walk u v) (n : Nat) : (p.drop n).Nil ↔ p.length <= n
参数：p : G.Walk u v；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma nil_drop_iff (p : G.Walk u v) (n : ℕ) : (p.drop n).Nil ↔ p.length ≤ n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]
/-
**SimpleGraph.Walk.drop_cons_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0) : (c
ons h p).drop n = (p.drop (n - 1)).copy (p.getVert_cons h hn).symm rfl
参数：h : G.Adj u v；p : G.Walk v w；n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.getVert_cons`：getVert_cons {u v w n} (p : G.Walk v w) (
h : G.Adj u v) (hn : n != 0) : (p.cons h).getVert n = p.getVert (n - 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.exists_add_one_eq`：∀ {a : ℕ}, (∃ n, n + 1 = a) ↔ 0 < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.drop.eq_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v) (n : ℕ),   p.drop n =     match v, p, n with     | .(u), Sim
pleGraph.Walk.nil,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma drop_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : ℕ) (hn : n ≠ 0) :
    (cons h p).drop n = (p.drop (n - 1)).copy (p.getVert_cons h hn).symm rfl := by
  apply ext_support
  obtain ⟨_, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.ne_zero_iff_zero_lt.mp hn)
  conv_lhs => unfold drop
  simp
/-
**SimpleGraph.Walk.darts_drop** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_drop (p : G.Walk u v) (n : Nat) : (p.drop n).darts = p.darts.drop n
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.darts_copy`：darts_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).darts = p.darts
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
-/
lemma darts_drop (p : G.Walk u v) (n : ℕ) : (p.drop n).darts = p.darts.drop n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]
/-
**SimpleGraph.Walk.edges_drop** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_drop (p : G.Walk u v) (n : Nat) : (p.drop n).edges = p.edges.drop n
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.edges_copy`：edges_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).edges = p.edges
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
-/
lemma edges_drop (p : G.Walk u v) (n : ℕ) : (p.drop n).edges = p.edges.drop n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

set_option backward.isDefEq.respectTransparency.types false in
/-- The walk obtained by taking the first `n` darts of a walk. -/
/-
**SimpleGraph.Walk.take** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take {u v : V} (p : G.Walk u v) (n : Nat) : G.Walk u (p.getVert n)
参数：p : G.Walk u v；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk obtained by taking the first `n` darts of a walk.
-/
def take {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk u (p.getVert n) :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]
/-
**SimpleGraph.Walk.take_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_zero (p : G.Walk u v) : p.take 0 = nil.copy rfl p.getVert_zero.symm
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma take_zero (p : G.Walk u v) : p.take 0 = nil.copy rfl p.getVert_zero.symm := by
  cases p <;> simp [take]

@[simp]
/-
**SimpleGraph.Walk.take_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_length (p : G.Walk u v) (n : Nat) : (p.take n).length = n ⊓ p.length
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
-/
lemma take_length (p : G.Walk u v) (n : ℕ) : (p.take n).length = n ⊓ p.length := by
  induction p generalizing n <;> cases n <;> simp [*, take]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.take_getVert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_getVert (p : G.Walk u v) (n m : Nat) : (p.take n).getVert m = p.getVe
rt (n ⊓ m)
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
-/
lemma take_getVert (p : G.Walk u v) (n m : ℕ) : (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m <;> cases n <;> cases m <;> simp [*, take]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.take_add_heq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_add_heq (p : G.Walk u v) (n m : Nat) : p.take (n + m) ≍ (p.take n).ap
pend ((p.drop n).take m)
参数：p : G.Walk u v；n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.take.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u : V} (
n : ℕ), SimpleGraph.Walk.nil.take n = SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma take_add_heq (p : G.Walk u v) (n m : ℕ) :
    p.take (n + m) ≍ (p.take n).append ((p.drop n).take m) := by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [take, drop]
  grind [drop_getVert]
/-
**SimpleGraph.Walk.take_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_add_eq (p : G.Walk u v) (n m : Nat) : p.take (n + m) = ((p.take n).ap
pend ((p.drop n).take m)).copy rfl (drop_getVert ..)
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SimpleGraph.Walk.drop_getVert`：drop_getVert (p : G.Walk u v) (n m : Nat)
 : (p.drop n).getVert m = p.getVert (n + m)
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用引理 `SimpleGraph.Walk.take_add_heq`：take_add_heq (p : G.Walk u v) (n m : Nat)
 : p.take (n + m) ≍ (p.take n).append ((p.drop n).take m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma take_add_eq (p : G.Walk u v) (n m : ℕ) :
    p.take (n + m) = ((p.take n).append ((p.drop n).take m)).copy rfl (drop_getVert ..) :=
  eq_of_heq <| take_add_heq .. |>.trans <| by simp [Walk.copy]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.nil_take_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_take_iff (p : G.Walk u v) (n : Nat) : (p.take n).Nil ↔ p.Nil ∨ n = 0
参数：p : G.Walk u v；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma nil_take_iff (p : G.Walk u v) (n : ℕ) : (p.take n).Nil ↔ p.Nil ∨ n = 0 := by
  cases p <;> cases n <;> simp [take]
/-
**SimpleGraph.Walk.support_take** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_take {u v} (p : G.Walk u v) (n : Nat) : (p.take n).support = p.sup
port.take (n + 1)
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
-/
lemma support_take {u v} (p : G.Walk u v) (n : ℕ) :
    (p.take n).support = p.support.take (n + 1) := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[deprecated (since := "2026-05-20")] alias take_support_eq_support_take_succ := support_take

@[simp]
/-
**SimpleGraph.Walk.take_take** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_take (p : G.Walk u v) (n m : Nat) : (p.take n).take m = (p.take (min 
n m)).copy rfl (p.take_getVert n m).symm
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.take_getVert`：take_getVert (p : G.Walk u v) (n m : Nat)
 : (p.take n).getVert m = p.getVert (n ⊓ m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.support_take`：support_take {u v} (p : G.Walk u v) (n : 
Nat) : (p.take n).support = p.support.take (n + 1)
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `Nat.min_assoc`：∀ (a b c : ℕ), min (min a b) c = min a (min b c)
· 使用定理 `Nat.min_left_comm`：∀ (a b c : ℕ), min a (min b c) = min b (min a c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma take_take (p : G.Walk u v) (n m : ℕ) :
    (p.take n).take m = (p.take (min n m)).copy rfl (p.take_getVert n m).symm := by
  apply ext_support
  simp [support_take, List.take_take, Nat.min_left_comm]
/-
**SimpleGraph.Walk.take_of_length_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：take_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) : p.take n 
= p.copy rfl (p.getVert_of_length_le h).symm
参数：h : p.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
· 使用定理 `SimpleGraph.Walk.length_cons`：length_cons {u v w : V} (h : G.Adj u v) (p
 : G.Walk v w) : (cons h p).length = p.length + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
· 使用定理 `SimpleGraph.Walk.cons_copy`：cons_copy {u v w v' w'} (h : G.Adj u v) (p :
 G.Walk v' w') (hv : v' = v) (hw : w' = w) : cons h (p.copy hv hw) = (Walk.cons 
(hv ▸ h) p).copy…
-/
lemma take_of_length_le {u v n} {p : G.Walk u v} (h : p.length ≤ n) :
    p.take n = p.copy rfl (p.getVert_of_length_le h).symm := by
  induction n generalizing p u with
  | zero => cases p <;> simp [take] at h ⊢
  | succ n ih =>
    cases p
    · simp [take]
    rw [length_cons, Nat.add_le_add_iff_right] at h
    simp [take, ih h]
/-
**SimpleGraph.Walk.take_cons_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0) : (c
ons h p).take n = cons h ((p.take <| n - 1).copy rfl (p.getVert_cons h hn).symm)
参数：h : G.Adj u v；p : G.Walk v w；n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.getVert_cons`：getVert_cons {u v w n} (p : G.Walk v w) (
h : G.Adj u v) (hn : n != 0) : (p.cons h).getVert n = p.getVert (n - 1)
-/
lemma take_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : ℕ) (hn : n ≠ 0) :
    (cons h p).take n = cons h ((p.take <| n - 1).copy rfl (p.getVert_cons h hn).symm) := by
  apply ext_support
  grind [support_copy, support_take]
/-
**SimpleGraph.Walk.darts_take** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_take (p : G.Walk u v) (n : Nat) : (p.take n).darts = p.darts.take n
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.darts_copy`：darts_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).darts = p.darts
-/
lemma darts_take (p : G.Walk u v) (n : ℕ) : (p.take n).darts = p.darts.take n := by
  induction p generalizing n <;> cases n <;> simp [*, take]
/-
**SimpleGraph.Walk.edges_take** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_take (p : G.Walk u v) (n : Nat) : (p.take n).edges = p.edges.take n
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_copy`：edges_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).edges = p.edges
-/
lemma edges_take (p : G.Walk u v) (n : ℕ) : (p.take n).edges = p.edges.take n := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]
/-
**SimpleGraph.Walk.penultimate_concat** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) : (p.concat h)
.penultimate = v
参数：p : G.Walk u v；h : G.Adj v t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_append`：getVert_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) (i : Nat) : (p.append q).getVert i = if i < p.length then 
p.getVert i else q.ge…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).penultimate = v := by simp [concat_eq_append, getVert_append]

@[simp]
/-
**SimpleGraph.Walk.snd_reverse** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.getVert_reverse`：getVert_reverse {u v : V} (p : G.Walk 
u v) (i : Nat) : p.reverse.getVert i = p.getVert (p.length - i)
-/
lemma snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate := by
  simpa using getVert_reverse p 1

@[simp]
/-
**SimpleGraph.Walk.penultimate_reverse** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.getVert_append`：getVert_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) (i : Nat) : (p.append q).getVert i = if i < p.length then 
p.getVert i else q.ge…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
-/
lemma penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd := by
  cases p <;> simp [snd, getVert_append]

/-- The walk obtained by removing the first dart of a walk. A nil walk stays nil. -/
/-
**SimpleGraph.Walk.tail** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：tail (p : G.Walk u v) : G.Walk (p.snd) v
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk obtained by removing the first dart of a walk. A nil walk stays nil.
-/
def tail (p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1

@[simp]
/-
**SimpleGraph.Walk.darts_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_tail {p : G.Walk u v} : p.tail.darts = p.darts.tail
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.darts_drop`：darts_drop (p : G.Walk u v) (n : Nat) : (p.
drop n).darts = p.darts.drop n
· 使用定理 `List.drop_one`：∀ {α : Type u_1} {l : List α}, List.drop 1 l = l.tail
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem darts_tail {p : G.Walk u v} : p.tail.darts = p.darts.tail := by
  simp [tail, darts_drop]

@[simp]
/-
**SimpleGraph.Walk.edges_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_tail {p : G.Walk u v} : p.tail.edges = p.edges.tail
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.edges_drop`：edges_drop (p : G.Walk u v) (n : Nat) : (p.
drop n).edges = p.edges.drop n
· 使用定理 `List.drop_one`：∀ {α : Type u_1} {l : List α}, List.drop 1 l = l.tail
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_tail {p : G.Walk u v} : p.tail.edges = p.edges.tail := by
  simp [tail, edges_drop]

@[simp]
/-
**SimpleGraph.Walk.drop_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_zero {u v} (p : G.Walk u v) : p.drop 0 = p.copy (getVert_zero p).symm
 rfl
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]
/-
**SimpleGraph.Walk.nil_drop_of_length_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：nil_drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) : (p.dr
op n).Nil
参数：h : p.length <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_eq_zero_iff`：length_eq_zero_iff {p : G.Walk u v}
 : p.length = 0 ↔ p.Nil
· 使用引理 `SimpleGraph.Walk.drop_length`：drop_length (p : G.Walk u v) (n : Nat) : (
p.drop n).length = p.length - n
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
-/
lemma nil_drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length ≤ n) :
    (p.drop n).Nil := by
  rw [← length_eq_zero_iff, drop_length, Nat.sub_eq_zero_of_le h]

@[simp]
/-
**SimpleGraph.Walk.drop_support_eq_support_drop_min** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : Nat) : (p.dro
p n).support = p.support.drop (n ⊓ p.length)
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
-/
lemma drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : ℕ) :
    (p.drop n).support = p.support.drop (n ⊓ p.length) := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

@[simp]
/-
**SimpleGraph.Walk.drop_drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：drop_drop (p : G.Walk u v) (n m : Nat) : (p.drop n).drop m = (p.drop (n + 
m)).copy (drop_getVert ..).symm rfl
参数：p : G.Walk u v；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.drop_getVert`：drop_getVert (p : G.Walk u v) (n m : Nat)
 : (p.drop n).getVert m = p.getVert (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SimpleGraph.Walk.drop_support_eq_support_drop_min`：drop_support_eq_suppo
rt_drop_min {u v} (p : G.Walk u v) (n : Nat) : (p.drop n).support = p.support.dr
op (n ⊓ p.length)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.Walk.drop_length`：drop_length (p : G.Walk u v) (n : Nat) : (
p.drop n).length = p.length - n
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
-/
theorem drop_drop (p : G.Walk u v) (n m : ℕ) :
    (p.drop n).drop m = (p.drop (n + m)).copy (drop_getVert ..).symm rfl := by
  apply ext_support
  simp_rw [support_copy, drop_support_eq_support_drop_min, drop_length, List.drop_drop]
  grind

@[simp]
/-
**SimpleGraph.Walk.append_take_drop_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：append_take_drop_eq (p : G.Walk u v) (n : Nat) : (p.take n).append (p.drop
 n) = p
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用引理 `SimpleGraph.Walk.support_take`：support_take {u v} (p : G.Walk u v) (n : 
Nat) : (p.take n).support = p.support.take (n + 1)
· 使用引理 `SimpleGraph.Walk.drop_support_eq_support_drop_min`：drop_support_eq_suppo
rt_drop_min {u v} (p : G.Walk u v) (n : Nat) : (p.drop n).support = p.support.dr
op (n ⊓ p.length)
· 使用定理 `List.tail_drop`：∀ {α : Type u_1} {l : List α} {i : ℕ}, (List.drop i l).t
ail = List.drop (i + 1) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `min_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a 
< b → min a b = a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.min_eq_right`：∀ {a b : ℕ}, b ≤ a → min a b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem append_take_drop_eq (p : G.Walk u v) (n : ℕ) : (p.take n).append (p.drop n) = p := by
  apply ext_support
  rw [support_append, support_take, drop_support_eq_support_drop_min,
    List.tail_drop]
  by_cases! h : n < p.length
  · simp [min_eq_left_of_lt h]
  · rw [Nat.min_eq_right h, ← length_support, List.drop_length]
    simp [h]

/-- The walk obtained by removing the last dart of a walk. A nil walk stays nil. -/
/-
**SimpleGraph.Walk.dropLast** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：dropLast (p : G.Walk u v) : G.Walk u p.penultimate
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk obtained by removing the last dart of a walk. A nil walk stays nil.
-/
def dropLast (p : G.Walk u v) : G.Walk u p.penultimate := p.take (p.length - 1)

@[simp]
/-
**SimpleGraph.Walk.tail_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：tail_nil : (@nil _ G v).tail = .nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tail_nil : (@nil _ G v).tail = .nil := rfl

@[simp]
/-
**SimpleGraph.Walk.tail_cons_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := rfl

@[simp]
/-
**SimpleGraph.Walk.tail_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：tail_cons (h : G.Adj u v) (p : G.Walk v w) : (p.cons h).tail = p.copy (get
Vert_zero p).symm rfl
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma tail_cons (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  cases p <;> rfl

@[simp]
/-
**SimpleGraph.Walk.dropLast_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：dropLast_nil : (@nil _ G v).dropLast = nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dropLast_nil : (@nil _ G v).dropLast = nil := rfl

@[simp]
/-
**SimpleGraph.Walk.dropLast_cons_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：dropLast_cons_nil (h : G.Adj u v) : (cons h nil).dropLast = nil
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dropLast_cons_nil (h : G.Adj u v) : (cons h nil).dropLast = nil := rfl

@[simp]
/-
**SimpleGraph.Walk.dropLast_cons_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：dropLast_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w')
 : (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast
参数：h : G.Adj u v；h₂ : G.Adj v w；p : G.Walk w w'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dropLast_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast := rfl
/-
**SimpleGraph.Walk.dropLast_cons_of_not_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：dropLast_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
 (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil 
_ _ hp).symm)
参数：h : G.Adj u v；p : G.Walk v w；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.penultimate_cons_of_not_nil`：penultimate_cons_of_not_ni
l (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) : (cons h p).penultimate = p.p
enultimate
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma dropLast_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil _ _ hp).symm) :=
  p.notNilRec (by simp) hp h

@[simp]
/-
**SimpleGraph.Walk.darts_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_dropLast {p : G.Walk u v} : p.dropLast.darts = p.darts.dropLast
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.darts_take`：darts_take (p : G.Walk u v) (n : Nat) : (p.
take n).darts = p.darts.take n
· 使用定理 `List.dropLast_eq_take`：∀ {α : Type u_1} {l : List α}, l.dropLast = List.
take (l.length - 1) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem darts_dropLast {p : G.Walk u v} : p.dropLast.darts = p.darts.dropLast := by
  simp [dropLast, darts_take, List.dropLast_eq_take]

@[simp]
/-
**SimpleGraph.Walk.edges_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_dropLast {p : G.Walk u v} : p.dropLast.edges = p.edges.dropLast
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.edges_take`：edges_take (p : G.Walk u v) (n : Nat) : (p.
take n).edges = p.edges.take n
· 使用定理 `List.dropLast_eq_take`：∀ {α : Type u_1} {l : List α}, l.dropLast = List.
take (l.length - 1) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_edges`：length_edges {u v : V} (p : G.Walk u v) :
 p.edges.length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_dropLast {p : G.Walk u v} : p.dropLast.edges = p.edges.dropLast := by
  simp [dropLast, edges_take, List.dropLast_eq_take]

@[simp]
/-
**SimpleGraph.Walk.dropLast_concat** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：dropLast_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) : (p.concat h).dr
opLast = p.copy rfl (by simp)
参数：p : G.Walk u v；h : G.Adj v t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.concat_cons`：concat_cons {u v w x : V} (h : G.Adj u v) 
(p : G.Walk v w) (h' : G.Adj w x) : (cons h p).concat h' = cons h (p.concat h')
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.penultimate_cons_of_not_nil`：penultimate_cons_of_not_ni
l (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) : (cons h p).penultimate = p.p
enultimate
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_concat`：length_concat {u v w : V} (p : G.Walk u 
v) (h : G.Adj v w) : (p.concat h).length = p.length + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `SimpleGraph.Walk.dropLast_cons_of_not_nil`：dropLast_cons_of_not_nil (h :
 G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) : (cons h p).dropLast = cons h (p.dr
opLast.copy rfl (penultimate_co…
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
· 使用定理 `SimpleGraph.Walk.copy.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v u' v' : V} (p p_1 : G.Walk u v),   p = p_1 → ∀ (hu : u = u') (hv : v = v'), p.
copy hu hv = p_1.copy …
· 使用定理 `SimpleGraph.Walk.copy_copy`：copy_copy {u v u' v' u'' v''} (p : G.Walk u 
v) (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') : (p.copy hu hv
).copy hu' hv' =…
· 使用定理 `SimpleGraph.Walk.cons_copy`：cons_copy {u v w v' w'} (h : G.Adj u v) (p :
 G.Walk v' w') (hv : v' = v) (hw : w' = w) : cons h (p.copy hv hw) = (Walk.cons 
(hv ▸ h) p).copy…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dropLast_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).dropLast = p.copy rfl (by simp) := by
  induction p
  · rfl
  · rw! [concat_cons, dropLast_cons_of_not_nil] <;>
      simp [*, ← length_eq_zero_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.cons_tail_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) : cons (p.adj_snd hp) p.tail 
= p
参数：p : G.Walk u v；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.cons_copy`：cons_copy {u v w v' w'} (h : G.Adj u v) (p :
 G.Walk v' w') (hv : v' = v) (hw : w' = w) : cons h (p.copy hv hw) = (Walk.cons 
(hv ▸ h) p).copy…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) :
    cons (p.adj_snd hp) p.tail = p := by
  cases p <;> simp at hp ⊢

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.concat_dropLast** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：concat_dropLast {p : G.Walk u v} (hp : G.Adj p.penultimate v) : p.dropLast
.concat hp = p
参数：hp : G.Adj p.penultimate v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma concat_dropLast {p : G.Walk u v} (hp : G.Adj p.penultimate v) : p.dropLast.concat hp = p := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp]
/-
**SimpleGraph.Walk.support_tail_of_not_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：support_tail_of_not_nil (p : G.Walk u v) (hp : ¬ p.Nil) : p.tail.support =
 p.support.tail
参数：p : G.Walk u v；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.cons_tail_eq`：cons_tail_eq (p : G.Walk u v) (hp : ¬ p.N
il) : cons (p.adj_snd hp) p.tail = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_tail_of_not_nil (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  simp [← p.cons_tail_eq hp]
/-
**SimpleGraph.Walk.cons_support_tail** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：cons_support_tail {p : G.Walk u v} (hp : ¬p.Nil) : u :: p.tail.support = p
.support
参数：hp : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `SimpleGraph.Walk.cons_tail_support`：cons_tail_support (p : G.Walk u v) :
 u :: p.support.tail = p.support
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_support_tail {p : G.Walk u v} (hp : ¬p.Nil) : u :: p.tail.support = p.support := by
  simp [hp]
/-
**SimpleGraph.Walk.support_dropLast_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：support_dropLast_concat {p : G.Walk u v} (hp : ¬p.Nil) : p.dropLast.suppor
t ++ [v] = p.support
参数：hp : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.support_concat`：support_concat (p : G.Walk u v) (h : G.
Adj v w) : (p.concat h).support = p.support ++ [w]
· 使用引理 `SimpleGraph.Walk.concat_dropLast`：concat_dropLast {p : G.Walk u v} (hp :
 G.Adj p.penultimate v) : p.dropLast.concat hp = p
-/
theorem support_dropLast_concat {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.support ++ [v] = p.support := by
  rw [← support_concat _ <| adj_penultimate hp, concat_dropLast]

@[simp]
/-
**SimpleGraph.Walk.support_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：support_dropLast {p : G.Walk u v} (hp : ¬p.Nil) : p.dropLast.support = p.s
upport.dropLast
参数：hp : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.support_dropLast_concat`：support_dropLast_concat {p : G
.Walk u v} (hp : ¬p.Nil) : p.dropLast.support ++ [v] = p.support
· 使用定理 `List.dropLast_append_of_ne_nil`：∀ {α : Type u} {l l' : List α}, l ≠ [] →
 (l' ++ l).dropLast = l' ++ l.dropLast
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_dropLast {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.support = p.support.dropLast := by
  simp [← support_dropLast_concat hp]

@[simp]
/-
**SimpleGraph.Walk.length_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_tail (p : G.Walk u v) : p.tail.length = p.length - 1
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
-/
theorem length_tail (p : G.Walk u v) : p.tail.length = p.length - 1 := by
  cases p <;> simp
/-
**SimpleGraph.Walk.length_tail_add_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：length_tail_add_one {p : G.Walk u v} (hp : ¬ p.Nil) : p.tail.length + 1 = 
p.length
参数：hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_cons`：length_cons {u v w : V} (h : G.Adj u v) (p
 : G.Walk v w) : (cons h p).length = p.length + 1
· 使用引理 `SimpleGraph.Walk.cons_tail_eq`：cons_tail_eq (p : G.Walk u v) (hp : ¬ p.N
il) : cons (p.adj_snd hp) p.tail = p
-/
lemma length_tail_add_one {p : G.Walk u v} (hp : ¬ p.Nil) :
    p.tail.length + 1 = p.length := by
  rw [← length_cons (p.adj_snd hp), cons_tail_eq _ hp]
/-
**SimpleGraph.Walk.length_dropLast_add_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：length_dropLast_add_one {p : G.Walk u v} (hp : ¬p.Nil) : p.dropLast.length
 + 1 = p.length
参数：hp : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_concat`：length_concat {u v w : V} (p : G.Walk u 
v) (h : G.Adj v w) : (p.concat h).length = p.length + 1
· 使用引理 `SimpleGraph.Walk.concat_dropLast`：concat_dropLast {p : G.Walk u v} (hp :
 G.Adj p.penultimate v) : p.dropLast.concat hp = p
-/
lemma length_dropLast_add_one {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.length + 1 = p.length := by
  rw [← length_concat _ <| p.adj_penultimate hp, concat_dropLast]

@[simp]
/-
**SimpleGraph.Walk.length_dropLast** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_dropLast (p : G.Walk u v) : p.dropLast.length = p.length - 1
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.Walk.length_dropLast_add_one`：length_dropLast_add_one {p : G
.Walk u v} (hp : ¬p.Nil) : p.dropLast.length + 1 = p.length
· 使用定理 `SimpleGraph.Walk.not_nil_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 : V} {h : G.Adj u v} {p : G.Walk v w}, ¬(SimpleGraph.Walk.cons h p).Nil
-/
lemma length_dropLast (p : G.Walk u v) : p.dropLast.length = p.length - 1 := by
  cases p <;> simp [← length_dropLast_add_one not_nil_cons]
/-
**SimpleGraph.Walk.getVert_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：getVert_dropLast {n} {p : G.Walk u v} (h : n < p.length) : p.dropLast.getV
ert n = p.getVert n
参数：h : n < p.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getVert_dropLast {n} {p : G.Walk u v} (h : n < p.length) :
    p.dropLast.getVert n = p.getVert n := by
  grind [getVert_eq_support_getElem, length_dropLast, support_dropLast]

@[simp]
/-
**SimpleGraph.Walk.reverse_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_tail (p : G.Walk u v) : p.tail.reverse = p.reverse.dropLast.copy r
fl p.penultimate_reverse
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.penultimate_reverse`：penultimate_reverse (p : G.Walk u 
v) : p.reverse.penultimate = p.snd
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.reverse_copy`：reverse_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).reverse = p.reverse.copy hv hu
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
· 使用定理 `SimpleGraph.Walk.support_dropLast`：support_dropLast {p : G.Walk u v} (hp
 : ¬p.Nil) : p.dropLast.support = p.support.dropLast
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.dropLast_append_of_ne_nil`：∀ {α : Type u} {l l' : List α}, l ≠ [] →
 (l' ++ l).dropLast = l' ++ l.dropLast
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
theorem reverse_tail (p : G.Walk u v) :
    p.tail.reverse = p.reverse.dropLast.copy rfl p.penultimate_reverse := by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    rw [support_copy]
    simp [-reverse_cons]

@[simp]
/-
**SimpleGraph.Walk.reverse_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：reverse_dropLast (p : G.Walk u v) : p.dropLast.reverse = p.reverse.tail.co
py p.snd_reverse rfl
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.snd_reverse`：snd_reverse (p : G.Walk u v) : p.reverse.s
nd = p.penultimate
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
· 使用定理 `SimpleGraph.Walk.support_dropLast`：support_dropLast {p : G.Walk u v} (hp
 : ¬p.Nil) : p.dropLast.support = p.support.dropLast
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dropLast_cons_of_ne_nil`：∀ {α : Type u} {x : α} {l : List α}, l ≠ [
] → (x :: l).dropLast = x :: l.dropLast
· 使用定理 `SimpleGraph.Walk.support_ne_nil`：support_ne_nil {u v : V} (p : G.Walk u 
v) : p.support != []
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `List.tail_append_of_ne_nil`：∀ {α : Type u_1} {xs ys : List α}, xs ≠ [] →
 (xs ++ ys).tail = xs.tail ++ ys
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.tail_reverse`：∀ {α : Type u_1} {l : List α}, l.reverse.tail = l.dro
pLast.reverse
-/
theorem reverse_dropLast (p : G.Walk u v) :
    p.dropLast.reverse = p.reverse.tail.copy p.snd_reverse rfl := by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    simp [-reverse_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]
/-
**SimpleGraph.Walk.Nil.tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Nil`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w}, p.Nil → p.t
ail.Nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
protected lemma Nil.tail {p : G.Walk v w} (hp : p.Nil) : p.tail.Nil := by
  cases p <;> simp at hp ⊢
/-
**SimpleGraph.Walk.not_nil_of_tail_not_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil
参数：hp : ¬ p.tail.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Walk.Nil.tail`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} 
{p : G.Walk v w}, p.Nil → p.tail.Nil
-/
lemma not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil := mt Nil.tail hp
/-
**SimpleGraph.Walk.Nil.dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Nil`
。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w}, p.Nil → p.d
ropLast.Nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
protected lemma Nil.dropLast {p : G.Walk v w} (hp : p.Nil) : p.dropLast.Nil := by
  cases p <;> simp at hp ⊢
/-
**SimpleGraph.Walk.nil_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v u' v' : V} {p : G.Walk u v} (hu : 
u = u') (hv : v = v'),   (p.copy hu hv).Nil = p.Nil
参数：hu : u = u'；hv : v = v'；p.copy hu hv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma nil_copy {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil = p.Nil := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.Nil.eq_copy_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.N
il`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (h : p.Nil),
 p = SimpleGraph.Walk.nil.copy ⋯ ⋯
参数：h : p.Nil。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nil.eq_copy_nil {p : G.Walk u v} (h : p.Nil) : p = Walk.nil.copy rfl h.eq := by
  grind [eq_nil_iff_nil, copy_rfl_rfl]
/-
**SimpleGraph.Walk.drop_of_length_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) : p.drop n 
= nil.copy rfl (p.getVert_of_length_le h)
参数：h : p.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.Nil.eq_copy_nil`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} {p : G.Walk u v} (h : p.Nil), p = SimpleGraph.Walk.nil.copy ⋯ ⋯
· 使用引理 `SimpleGraph.Walk.nil_drop_of_length_le`：nil_drop_of_length_le {u v n} {p
 : G.Walk u v} (h : p.length <= n) : (p.drop n).Nil
-/
lemma drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length ≤ n) :
    p.drop n = nil.copy rfl (p.getVert_of_length_le h) :=
  (nil_drop_of_length_le h).eq_copy_nil
/-
**SimpleGraph.Walk.getVert_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w x : V} (p : G.Walk u v) (i : ℕ) 
(h : u = w) (h' : v = x),   (p.copy h h').getVert i = p.getVert i
参数：p : G.Walk u v；i : ℕ；h : u = w；h' : v = x；p.copy h h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.getVert_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {n : ℕ} (p : G.Walk u v), p.t
ail.getVert n = p.getVert (n + 1)
参数：p : G.Walk u v；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.getVert_copy`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x),   (p.copy h h').getVe
rt i = p.getVert i
-/
@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) :
    p.tail.getVert n = p.getVert (n + 1) := by
  cases p <;> simp
/-
**SimpleGraph.Walk.getVert_mem_tail_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, ¬p.Nil → ∀ 
{i : ℕ}, i ≠ 0 → p.getVert i ∈ p.support.tail
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_tail`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V} {n : ℕ} (p : G.Walk u v), p.tail.getVert n = p.getVert (n + 1)
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `SimpleGraph.Walk.getVert_mem_support`：getVert_mem_support {u v : V} (p :
 G.Walk u v) (i : Nat) : p.getVert i in p.support
-/
lemma getVert_mem_tail_support {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) :
    ∀ {i : ℕ}, i ≠ 0 → p.getVert i ∈ p.support.tail
  | i + 1, _ => by
    rw [← getVert_tail, ← p.support_tail_of_not_nil hp]
    exact getVert_mem_support ..
/-
**SimpleGraph.Walk.support_injective** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：support_injective {u v : V} : (support (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
-/
lemma support_injective {u v : V} : (support (G := G) (u := u) (v := v)).Injective :=
  fun _ _ ↦ ext_support
/-
**SimpleGraph.Walk.ext_getVert_le_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：ext_getVert_le_length {u v} {p q : G.Walk u v} (hl : p.length = q.length) 
(h : forall k <= p.length, p.getVert k = q.getVert k) : p = q
参数：hl : p.length = q.length；h : forall k <= p.length, p.getVert k = q.getVert k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem?`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {n : ℕ} (p : G.Walk u v), n ≤ p.length → some (p.getVert n) =
 p.support[n]?
· 使用定理 `List.getElem?_eq_none_iff`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l[i]? 
= none ↔ l.length ≤ i
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.ext_getElem?_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ = l₂ ↔ ∀ (i
 : ℕ), l₁[i]? = l₂[i]?
-/
lemma ext_getVert_le_length {u v} {p q : G.Walk u v} (hl : p.length = q.length)
    (h : ∀ k ≤ p.length, p.getVert k = q.getVert k) :
    p = q := by
  suffices ∀ k : ℕ, p.support[k]? = q.support[k]? by
    exact ext_support <| List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk, ← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | inr hk =>
    replace hk : p.length + 1 ≤ k := hk
    have ht : q.length + 1 ≤ k := hl ▸ hk
    rw [← length_support, ← List.getElem?_eq_none_iff] at hk ht
    rw [hk, ht]
/-
**SimpleGraph.Walk.ext_getVert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：ext_getVert {u v} {p q : G.Walk u v} (h : forall k, p.getVert k = q.getVer
t k) : p = q
参数：h : forall k, p.getVert k = q.getVert k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `SimpleGraph.Walk.ext_getVert_le_length`：ext_getVert_le_length {u v} {p q
 : G.Walk u v} (hl : p.length = q.length) (h : forall k <= p.length, p.getVert k
 = q.getVert k) : p = q
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
lemma ext_getVert {u v} {p q : G.Walk u v} (h : ∀ k, p.getVert k = q.getVert k) :
    p = q := by
  wlog hpq : p.length ≤ q.length generalizing p q
  · exact (this (h · |>.symm) (le_of_not_ge hpq)).symm
  refine ext_getVert_le_length (hpq.antisymm ?_) fun k _ ↦ h k
  by_contra!
  exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])

open scoped List in
/-
**SimpleGraph.Walk.support_tail_perm_support_dropLast** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：support_tail_perm_support_dropLast (p : G.Walk u u) : p.tail.support ~ p.d
ropLast.support
参数：p : G.Walk u u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.perm_cons`：∀ {α : Type u_1} (a : α) {l₁ l₂ : List α}, (a :: l₁).Per
m (a :: l₂) ↔ l₁.Perm l₂
· 使用定理 `List.perm_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ ↔ l₂.Perm 
l₁
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.perm_append_singleton`：∀ {α : Type u_1} (a : α) (l : List α), (l ++
 [a]).Perm (a :: l)
· 使用引理 `SimpleGraph.Walk.cons_support_tail`：cons_support_tail {p : G.Walk u v} (
hp : ¬p.Nil) : u :: p.tail.support = p.support
· 使用定理 `SimpleGraph.Walk.not_nil_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 : V} {h : G.Adj u v} {p : G.Walk v w}, ¬(SimpleGraph.Walk.cons h p).Nil
· 使用定理 `SimpleGraph.Walk.support_dropLast_concat`：support_dropLast_concat {p : G
.Walk u v} (hp : ¬p.Nil) : p.dropLast.support ++ [v] = p.support
-/
theorem support_tail_perm_support_dropLast (p : G.Walk u u) :
    p.tail.support ~ p.dropLast.support := by
  cases p with | nil => rfl | cons h p
  grw [← List.perm_cons u, List.perm_comm, ← List.perm_append_singleton,
    cons_support_tail not_nil_cons, support_dropLast_concat not_nil_cons]

open scoped List in
/-
**SimpleGraph.Walk.tail_support_perm_dropLast_support** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：tail_support_perm_dropLast_support (p : G.Walk u u) : p.support.tail ~ p.s
upport.dropLast
参数：p : G.Walk u u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `SimpleGraph.Walk.support_dropLast`：support_dropLast {p : G.Walk u v} (hp
 : ¬p.Nil) : p.dropLast.support = p.support.dropLast
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.Walk.support_tail_perm_support_dropLast`：support_tail_perm_s
upport_dropLast (p : G.Walk u u) : p.tail.support ~ p.dropLast.support
-/
theorem tail_support_perm_dropLast_support (p : G.Walk u u) :
    p.support.tail ~ p.support.dropLast := by
  cases p with | nil => rfl | cons h p
  simpa using support_tail_perm_support_dropLast <| p.cons h

end Walk

end SimpleGraph

