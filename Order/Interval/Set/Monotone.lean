/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Monotonicity on intervals

In this file we prove that `Set.Ici` etc. are monotone/antitone functions. We also prove some lemmas
about functions monotone on intervals in `SuccOrder`s.
-/

public section


open Set

section Ixx

variable {α β : Type*} [Preorder α] [Preorder β] {f g : α → β} {s : Set α}

/-
**antitone_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_Ici : Antitone (Ici : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
-/
theorem antitone_Ici : Antitone (Ici : α → Set α) := fun _ _ => Ici_subset_Ici.2
/-
**monotone_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_Iic : Monotone (Iic : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
-/
theorem monotone_Iic : Monotone (Iic : α → Set α) := fun _ _ => Iic_subset_Iic.2
/-
**antitone_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_Ioi : Antitone (Ioi : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
-/
theorem antitone_Ioi : Antitone (Ioi : α → Set α) := fun _ _ => Ioi_subset_Ioi
/-
**monotone_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_Iio : Monotone (Iio : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
-/
theorem monotone_Iio : Monotone (Iio : α → Set α) := fun _ _ => Iio_subset_Iio
/-
**Monotone.Ici** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → Antitone fun x => Set.Ici (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `antitone_Ici`：antitone_Ici : Antitone (Ici : α -> Set α)
-/
protected theorem Monotone.Ici (hf : Monotone f) : Antitone fun x => Ici (f x) :=
  antitone_Ici.comp_monotone hf
/-
**MonotoneOn.Ici** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x => Set.Ici (f x)) 
s
参数：fun x => Set.Ici (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotoneOn`：Antitone.comp_monotoneOn (hg : Antitone g) (hf
 : MonotoneOn f s) : AntitoneOn (g ∘ f) s
· 使用定理 `antitone_Ici`：antitone_Ici : Antitone (Ici : α -> Set α)
-/
protected theorem MonotoneOn.Ici (hf : MonotoneOn f s) : AntitoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_monotoneOn hf
/-
**Antitone.Ici** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Antitone f → Monotone fun x => Set.Ici (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `antitone_Ici`：antitone_Ici : Antitone (Ici : α -> Set α)
-/
protected theorem Antitone.Ici (hf : Antitone f) : Monotone fun x => Ici (f x) :=
  antitone_Ici.comp hf
/-
**AntitoneOn.Ici** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x => Set.Ici (f x)) 
s
参数：fun x => Set.Ici (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_antitoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用定理 `antitone_Ici`：antitone_Ici : Antitone (Ici : α -> Set α)
-/
protected theorem AntitoneOn.Ici (hf : AntitoneOn f s) : MonotoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_antitoneOn hf
/-
**Monotone.Iic** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → Monotone fun x => Set.Iic (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `monotone_Iic`：monotone_Iic : Monotone (Iic : α -> Set α)
-/
protected theorem Monotone.Iic (hf : Monotone f) : Monotone fun x => Iic (f x) :=
  monotone_Iic.comp hf
/-
**MonotoneOn.Iic** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x => Set.Iic (f x)) 
s
参数：fun x => Set.Iic (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_monotoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用定理 `monotone_Iic`：monotone_Iic : Monotone (Iic : α -> Set α)
-/
protected theorem MonotoneOn.Iic (hf : MonotoneOn f s) : MonotoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_monotoneOn hf
/-
**Antitone.Iic** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Antitone f → Antitone fun x => Set.Iic (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用定理 `monotone_Iic`：monotone_Iic : Monotone (Iic : α -> Set α)
-/
protected theorem Antitone.Iic (hf : Antitone f) : Antitone fun x => Iic (f x) :=
  monotone_Iic.comp_antitone hf
/-
**AntitoneOn.Iic** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x => Set.Iic (f x)) 
s
参数：fun x => Set.Iic (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitoneOn`：Monotone.comp_antitoneOn (hg : Monotone g) (hf
 : AntitoneOn f s) : AntitoneOn (g ∘ f) s
· 使用定理 `monotone_Iic`：monotone_Iic : Monotone (Iic : α -> Set α)
-/
protected theorem AntitoneOn.Iic (hf : AntitoneOn f s) : AntitoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_antitoneOn hf
/-
**Monotone.Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → Antitone fun x => Set.Ioi (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `antitone_Ioi`：antitone_Ioi : Antitone (Ioi : α -> Set α)
-/
protected theorem Monotone.Ioi (hf : Monotone f) : Antitone fun x => Ioi (f x) :=
  antitone_Ioi.comp_monotone hf
/-
**MonotoneOn.Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x => Set.Ioi (f x)) 
s
参数：fun x => Set.Ioi (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotoneOn`：Antitone.comp_monotoneOn (hg : Antitone g) (hf
 : MonotoneOn f s) : AntitoneOn (g ∘ f) s
· 使用定理 `antitone_Ioi`：antitone_Ioi : Antitone (Ioi : α -> Set α)
-/
protected theorem MonotoneOn.Ioi (hf : MonotoneOn f s) : AntitoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_monotoneOn hf
/-
**Antitone.Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Antitone f → Monotone fun x => Set.Ioi (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `antitone_Ioi`：antitone_Ioi : Antitone (Ioi : α -> Set α)
-/
protected theorem Antitone.Ioi (hf : Antitone f) : Monotone fun x => Ioi (f x) :=
  antitone_Ioi.comp hf
/-
**AntitoneOn.Ioi** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x => Set.Ioi (f x)) 
s
参数：fun x => Set.Ioi (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_antitoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用定理 `antitone_Ioi`：antitone_Ioi : Antitone (Ioi : α -> Set α)
-/
protected theorem AntitoneOn.Ioi (hf : AntitoneOn f s) : MonotoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_antitoneOn hf
/-
**Monotone.Iio** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → Monotone fun x => Set.Iio (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `monotone_Iio`：monotone_Iio : Monotone (Iio : α -> Set α)
-/
protected theorem Monotone.Iio (hf : Monotone f) : Monotone fun x => Iio (f x) :=
  monotone_Iio.comp hf
/-
**MonotoneOn.Iio** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x => Set.Iio (f x)) 
s
参数：fun x => Set.Iio (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_monotoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用定理 `monotone_Iio`：monotone_Iio : Monotone (Iio : α -> Set α)
-/
protected theorem MonotoneOn.Iio (hf : MonotoneOn f s) : MonotoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_monotoneOn hf
/-
**Antitone.Iio** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Antitone f → Antitone fun x => Set.Iio (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用定理 `monotone_Iio`：monotone_Iio : Monotone (Iio : α -> Set α)
-/
protected theorem Antitone.Iio (hf : Antitone f) : Antitone fun x => Iio (f x) :=
  monotone_Iio.comp_antitone hf
/-
**AntitoneOn.Iio** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x => Set.Iio (f x)) 
s
参数：fun x => Set.Iio (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitoneOn`：Monotone.comp_antitoneOn (hg : Monotone g) (hf
 : AntitoneOn f s) : AntitoneOn (g ∘ f) s
· 使用定理 `monotone_Iio`：monotone_Iio : Monotone (Iio : α -> Set α)
-/
protected theorem AntitoneOn.Iio (hf : AntitoneOn f s) : AntitoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_antitoneOn hf
/-
**Monotone.Icc** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Monotone f → Antitone g → Antitone fun x => Set.Icc (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.inter`：Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Ant
itone f) (hg : Antitone g) : Antitone fun x => f x inter g x
· 使用定理 `Monotone.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Antitone fun x => Set.Ici (f x)
· 使用定理 `Antitone.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Antitone fun x => Set.Iic (f x)
-/
protected theorem Monotone.Icc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic
/-
**MonotoneOn.Icc** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn g s → AntitoneOn (fun x
 => Set.Icc (f x) (g x)) s
参数：fun x => Set.Icc (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.inter`：AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x in
ter g …
· 使用定理 `MonotoneOn.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x 
=> S…
· 使用定理 `AntitoneOn.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x 
=> S…
-/
protected theorem MonotoneOn.Icc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic
/-
**Antitone.Icc** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set.Icc (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `Antitone.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Monotone fun x => Set.Ici (f x)
· 使用定理 `Monotone.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iic (f x)
-/
protected theorem Antitone.Icc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic
/-
**AntitoneOn.Icc** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn g s → MonotoneOn (fun x
 => Set.Icc (f x) (g x)) s
参数：fun x => Set.Icc (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.inter`：MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x in
ter g …
· 使用定理 `AntitoneOn.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x 
=> S…
· 使用定理 `MonotoneOn.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x 
=> S…
-/
protected theorem AntitoneOn.Icc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic
/-
**Monotone.Ico** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Monotone f → Antitone g → Antitone fun x => Set.Ico (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.inter`：Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Ant
itone f) (hg : Antitone g) : Antitone fun x => f x inter g x
· 使用定理 `Monotone.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Antitone fun x => Set.Ici (f x)
· 使用定理 `Antitone.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Antitone fun x => Set.Iio (f x)
-/
protected theorem Monotone.Ico (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio
/-
**MonotoneOn.Ico** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn g s → AntitoneOn (fun x
 => Set.Ico (f x) (g x)) s
参数：fun x => Set.Ico (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.inter`：AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x in
ter g …
· 使用定理 `MonotoneOn.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x 
=> S…
· 使用定理 `AntitoneOn.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x 
=> S…
-/
protected theorem MonotoneOn.Ico (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio
/-
**Antitone.Ico** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set.Ico (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `Antitone.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Monotone fun x => Set.Ici (f x)
· 使用定理 `Monotone.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iio (f x)
-/
protected theorem Antitone.Ico (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio
/-
**AntitoneOn.Ico** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn g s → MonotoneOn (fun x
 => Set.Ico (f x) (g x)) s
参数：fun x => Set.Ico (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.inter`：MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x in
ter g …
· 使用定理 `AntitoneOn.Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x 
=> S…
· 使用定理 `MonotoneOn.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x 
=> S…
-/
protected theorem AntitoneOn.Ico (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio
/-
**Monotone.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Monotone f → Antitone g → Antitone fun x => Set.Ioc (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.inter`：Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Ant
itone f) (hg : Antitone g) : Antitone fun x => f x inter g x
· 使用定理 `Monotone.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Antitone fun x => Set.Ioi (f x)
· 使用定理 `Antitone.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Antitone fun x => Set.Iic (f x)
-/
protected theorem Monotone.Ioc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic
/-
**MonotoneOn.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn g s → AntitoneOn (fun x
 => Set.Ioc (f x) (g x)) s
参数：fun x => Set.Ioc (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.inter`：AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x in
ter g …
· 使用定理 `MonotoneOn.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x 
=> S…
· 使用定理 `AntitoneOn.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x 
=> S…
-/
protected theorem MonotoneOn.Ioc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic
/-
**Antitone.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set.Ioc (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `Antitone.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Monotone fun x => Set.Ioi (f x)
· 使用定理 `Monotone.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iic (f x)
-/
protected theorem Antitone.Ioc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic
/-
**AntitoneOn.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn g s → MonotoneOn (fun x
 => Set.Ioc (f x) (g x)) s
参数：fun x => Set.Ioc (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.inter`：MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x in
ter g …
· 使用定理 `AntitoneOn.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x 
=> S…
· 使用定理 `MonotoneOn.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x 
=> S…
-/
protected theorem AntitoneOn.Ioc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic
/-
**Monotone.Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Monotone f → Antitone g → Antitone fun x => Set.Ioo (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.inter`：Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Ant
itone f) (hg : Antitone g) : Antitone fun x => f x inter g x
· 使用定理 `Monotone.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Antitone fun x => Set.Ioi (f x)
· 使用定理 `Antitone.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Antitone fun x => Set.Iio (f x)
-/
protected theorem Monotone.Ioo (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio
/-
**MonotoneOn.Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn g s → AntitoneOn (fun x
 => Set.Ioo (f x) (g x)) s
参数：fun x => Set.Ioo (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.inter`：AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x in
ter g …
· 使用定理 `MonotoneOn.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (fun x 
=> S…
· 使用定理 `AntitoneOn.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (fun x 
=> S…
-/
protected theorem MonotoneOn.Ioo (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio
/-
**Antitone.Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set.Ioo (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.inter`：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x inter g x
· 使用定理 `Antitone.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Monotone fun x => Set.Ioi (f x)
· 使用定理 `Monotone.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iio (f x)
-/
protected theorem Antitone.Ioo (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio
/-
**AntitoneOn.Ioo** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f g : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn g s → MonotoneOn (fun x
 => Set.Ioo (f x) (g x)) s
参数：fun x => Set.Ioo (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.inter`：MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : 
Set β} (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x in
ter g …
· 使用定理 `AntitoneOn.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (fun x 
=> S…
· 使用定理 `MonotoneOn.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (fun x 
=> S…
-/
protected theorem AntitoneOn.Ioo (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

end Ixx

section iUnion

variable {α β : Type*} [SemilatticeSup α] [LinearOrder β] {f g : α → β} {a b : β}

/-
**iUnion_Ioo_of_mono_of_isGLB_of_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hf : Antitone f) (hg : Monotone g) (
ha : IsGLB (range f) a) (hb : IsLUB (range g) b) : ⋃ x, Ioo (f x) (g x) = Ioo a 
b
参数：hf : Antitone f；hg : Monotone g；ha : IsGLB (range f) a；hb : IsLUB (range g) b
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_inter_of_monotone`：iUnion_inter_of_monotone {ι α} [Preorder ι
] [IsDirectedOrder ι] {s t : ι -> Set α} (hs : Monotone s) (ht : Monotone t) : ⋃
 i, s i inter t i …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Antitone.Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Antitone f → Monotone fun x => Set.Ioi (f x)
· 使用定理 `Monotone.Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iio (f x)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `IsGLB.iUnion_Ioi_eq`：IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, 
Ioi (f x) = Ioi a
· 使用定理 `IsLUB.iUnion_Iio_eq`：IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, 
Iio (f x) = Iio a
-/
theorem iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hf : Antitone f) (hg : Monotone g)
    (ha : IsGLB (range f) a) (hb : IsLUB (range g) b) : ⋃ x, Ioo (f x) (g x) = Ioo a b :=
  calc
    ⋃ x, Ioo (f x) (g x) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) :=
      iUnion_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a ∩ Iio b := congr_arg₂ (· ∩ ·) ha.iUnion_Ioi_eq hb.iUnion_Iio_eq

end iUnion

section SuccOrder

open Order

variable {α β : Type*} [PartialOrder α] [Preorder β] {ψ : α → β}

/-- A function `ψ` on a `SuccOrder` is strictly monotone before some `n` if for all `m` such that
`m < n`, we have `ψ m < ψ (succ m)`. -/
/-
**strictMonoOn_Iic_of_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_Iic_of_lt_succ [SuccOrder α] [IsSuccArchimedean α] {n : α} (h
ψ : forall m, m < n -> ψ m < ψ (succ m)) : StrictMonoOn ψ (Set.Iic n)
参数：hψ : forall m, m < n -> ψ m < ψ (succ m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_lt_succ`：strictMonoOn_of_lt_succ (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a < f (succ a)) : StrictM
onoOn f s
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b

--- 原说明 ---
A function `ψ` on a `SuccOrder` is strictly monotone before some `n` if for all 
`m` such that
`m < n`, we have `ψ m < ψ (succ m)`.
-/
theorem strictMonoOn_Iic_of_lt_succ [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ m < ψ (succ m)) : StrictMonoOn ψ (Set.Iic n) :=
  strictMonoOn_of_lt_succ ordConnected_Iic fun _a ha' _ ha ↦
    hψ _ <| (succ_le_iff_of_not_isMax ha').1 ha
/-
**strictAntiOn_Iic_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_Iic_of_succ_lt [SuccOrder α] [IsSuccArchimedean α] {n : α} (h
ψ : forall m, m < n -> ψ (succ m) < ψ m) : StrictAntiOn ψ (Set.Iic n)
参数：hψ : forall m, m < n -> ψ (succ m) < ψ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMonoOn_Iic_of_lt_succ`：strictMonoOn_Iic_of_lt_succ [SuccOrder α] [
IsSuccArchimedean α] {n : α} (hψ : forall m, m < n -> ψ m < ψ (succ m)) : Strict
MonoOn ψ (Set.Iic…
-/
theorem strictAntiOn_Iic_of_succ_lt [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ (succ m) < ψ m) : StrictAntiOn ψ (Set.Iic n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij
/-
**strictMonoOn_Ici_of_pred_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_Ici_of_pred_lt [PredOrder α] [IsPredArchimedean α] {n : α} (h
ψ : forall m, n < m -> ψ (pred m) < ψ m) : StrictMonoOn ψ (Set.Ici n)
参数：hψ : forall m, n < m -> ψ (pred m) < ψ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMonoOn_Iic_of_lt_succ`：strictMonoOn_Iic_of_lt_succ [SuccOrder α] [
IsSuccArchimedean α] {n : α} (hψ : forall m, m < n -> ψ m < ψ (succ m)) : Strict
MonoOn ψ (Set.Iic…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
-/
theorem strictMonoOn_Ici_of_pred_lt [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ (pred m) < ψ m) : StrictMonoOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij
/-
**strictAntiOn_Ici_of_lt_pred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_Ici_of_lt_pred [PredOrder α] [IsPredArchimedean α] {n : α} (h
ψ : forall m, n < m -> ψ m < ψ (pred m)) : StrictAntiOn ψ (Set.Ici n)
参数：hψ : forall m, n < m -> ψ m < ψ (pred m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictAntiOn_Iic_of_succ_lt`：strictAntiOn_Iic_of_succ_lt [SuccOrder α] [
IsSuccArchimedean α] {n : α} (hψ : forall m, m < n -> ψ (succ m) < ψ m) : Strict
AntiOn ψ (Set.Iic…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
-/
theorem strictAntiOn_Ici_of_lt_pred [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ m < ψ (pred m)) : StrictAntiOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

end SuccOrder

section LinearOrder

open Order

variable {α : Type*} [LinearOrder α]

/-
**StrictMonoOn.Iic_id_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n
 : α} {φ : α -> α} (hφ : StrictMonoOn φ (Set.Iic n)) : forall m <= n, m <= φ m
参数：hφ : StrictMonoOn φ (Set.Iic n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec_bot`：Succ.rec_bot (p : α -> Prop) (hbot : p ⊥) (hsucc : forall 
a, p a -> p (succ a)) (a : α) : p a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : a <= succ b ↔ a = suc
c b ∨ a <= b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Iic n)) : ∀ m ≤ n, m ≤ φ m := by
  revert hφ
  refine
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) → ∀ m ≤ n, m ≤ φ m)
      (fun _ _ hm => hm.trans bot_le) ?_ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_isMax.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    nth_grw 1 [ih]
    refine succ_le_of_lt (hφ (le_succ _) le_rfl ?_)
    exact lt_succ_of_not_isMax hk
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h
/-
**StrictMonoOn.Ici_le_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.Ici_le_id [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n
 : α} {φ : α -> α} (hφ : StrictMonoOn φ (Set.Ici n)) : forall m, n <= m -> φ m <
= m
参数：hφ : StrictMonoOn φ (Set.Ici n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.Iic_id_le`：StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArch
imedean α] [OrderBot α] {n : α} {φ : α -> α} (hφ : StrictMonoOn φ (Set.Iic n)) :
 forall m <=…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
-/
theorem StrictMonoOn.Ici_le_id [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Ici n)) : ∀ m, n ≤ m → φ m ≤ m :=
  StrictMonoOn.Iic_id_le (α := αᵒᵈ) fun _ hi _ hj hij => hφ hj hi hij

end LinearOrder

