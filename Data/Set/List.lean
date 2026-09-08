/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Defs

/-!
# Lemmas about `List`s and `Set.range`

In this file we prove lemmas about range of some operations on lists.
-/

public section


open List

variable {α β : Type*} (l : List α)

namespace Set

/-
**Set.range_list_map** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_map (f : α -> β) : range (map f) = { l | forall x in l, x in ra
nge f }
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `List.forall_mem_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α} {P : β → Prop}, (∀ i ∈ List.map f l, P i) ↔ ∀ j ∈ l, P (f j)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `List.subset_cons_self`：∀ {α : Type u_1} (a : α) (l : List α), l ⊆ a :: l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem range_list_map (f : α → β) : range (map f) = { l | ∀ x ∈ l, x ∈ range f } := by
  refine antisymm (range_subset_iff.2 fun l => forall_mem_map.2 fun y _ => mem_range_self _)
      fun l hl => ?_
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ihl =>
    rcases ihl fun x hx => hl x <| subset_cons_self _ _ hx with ⟨l, rfl⟩
    rcases hl a mem_cons_self with ⟨a, rfl⟩
    exact ⟨a :: l, map_cons⟩
/-
**Set.range_list_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_map_coe (s : Set α) : range (map ((↑) : s -> α)) = { l | forall
 x in l, x in s }
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_list_map`：range_list_map (f : α -> β) : range (map f) = { l | 
forall x in l, x in range f }
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_list_map_coe (s : Set α) : range (map ((↑) : s → α)) = { l | ∀ x ∈ l, x ∈ s } := by
  rw [range_list_map, Subtype.range_coe]

@[simp]
/-
**Set.range_list_get** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_get : range l.get = { x | x in l }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `List.mem_iff_get`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ n, l.
get n = a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_list_get : range l.get = { x | x ∈ l } := by
  ext x
  rw [mem_ofPred_eq, mem_iff_get, mem_range]
/-
**Set.range_list_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_getElem? : range (l[·]? : Nat -> Option α) = insert none (some 
'' { x | x in l })
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_list_getElem? :
    range (l[·]? : ℕ → Option α) = insert none (some '' { x | x ∈ l }) := by
  rw [← range_list_get, ← range_comp]
  refine (range_subset_iff.2 fun n => ?_).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · exact (le_or_gt l.length n).imp getElem?_eq_none_iff.mpr
      (fun hlt => ⟨⟨_, hlt⟩, (getElem?_eq_getElem hlt).symm⟩)
  · exact ⟨_, getElem?_eq_none_iff.mpr le_rfl⟩
  · exact range_subset_iff.2 fun k => ⟨_, getElem?_eq_getElem _⟩

@[simp]
/-
**Set.range_list_getD** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_getD (d : α) : (range fun n : Nat => l[n]?.getD d) = insert d {
 x | x in l }
参数：d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.range_list_getElem?`：∀ {α : Type u_1} (l : List α), (Set.range fun x
 => l[x]?) = insert none (some '' {x | x ∈ l})
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_list_getD (d : α) : (range fun n : Nat => l[n]?.getD d) = insert d { x | x ∈ l } :=
  calc
    (range fun n => l[n]?.getD d) = (fun o : Option α => o.getD d) '' range (l[·]?) := by
      simp only [← range_comp, Function.comp_def]
      rfl
    _ = insert d { x | x ∈ l } := by
      simp only [Option.getD, range_list_getElem?, image_insert_eq, image_image, image_id']

@[simp]
/-
**Set.range_list_getI** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_list_getI [Inhabited α] (l : List α) : range l.getI = insert default
 { x | x in l }
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `Set.range_list_getD`：range_list_getD (d : α) : (range fun n : Nat => l[n
]?.getD d) = insert d { x | x in l }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_list_getI [Inhabited α] (l : List α) :
    range l.getI = insert default { x | x ∈ l } := by
  unfold List.getI
  simp

end Set

/-- If each element of a list can be lifted to some type, then the whole list can be
lifted to this type. -/
/-
**List.canLift** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：List.canLift (c) (p) [CanLift α β c p] : CanLift (List α) (List β) (List.m
ap c) fun l => forall x in l, p x where prf l H
参数：c；p。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Set.range_list_map`：range_list_map (f : α -> β) : range (map f) = { l | 
forall x in l, x in range f }
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…

--- 原说明 ---
If each element of a list can be lifted to some type, then the whole list can be
lifted to this type.
-/
instance List.canLift (c) (p) [CanLift α β c p] :
    CanLift (List α) (List β) (List.map c) fun l => ∀ x ∈ l, p x where
  prf l H := by
    rw [← Set.mem_range, Set.range_list_map]
    exact fun a ha => CanLift.prf a (H a ha)
