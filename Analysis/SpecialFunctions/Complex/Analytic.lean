/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Various complex special functions are analytic

`log`, and `cpow` are analytic, since they are differentiable.
-/

public section

open Complex Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {f g : E -> Complex} {z : Complex} {x : E} {s : Set E}

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
/--
theorem `analyticAt_clog` / 定理 `analyticAt_clog`

English:
theorem analyticAt_clog
  given: (m : z in slitPlane)
  statement: AnalyticAt Complex log z
  proof: by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

中文:
定理 analyticAt_clog
  条件: (m : z in slitPlane)
  结论: AnalyticAt Complex log z
  证明: by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

Depends on / 依赖: analyticAt_iff_eventually_differentiableAt, differentiableAt_id, differentiableAt_id.clog, eventually_mem, filter_upwards, isOpen_slitPlane, isOpen_slitPlane.eventually_mem
-/
theorem analyticAt_clog (m : z in slitPlane) : AnalyticAt Complex log z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
/--
theorem `AnalyticAt.clog` / 定理 `AnalyticAt.clog`

English:
theorem AnalyticAt.clog
  given: (fa : AnalyticAt Complex f x) (m : f x in slitPlane)
  proof: (analyticAt_clog m).comp fa

中文:
定理 AnalyticAt.clog
  条件: (fa : AnalyticAt Complex f x) (m : f x in slitPlane)
  证明: (analyticAt_clog m).comp fa

Depends on / 依赖: analyticAt_clog
-/
theorem AnalyticAt.clog (fa : AnalyticAt Complex f x) (m : f x in slitPlane) :
    AnalyticAt Complex (fun z => log (f z)) x :=
  (analyticAt_clog m).comp fa

/--
theorem `AnalyticWithinAt.clog` / 定理 `AnalyticWithinAt.clog`

English:
theorem AnalyticWithinAt.clog
  given: (fa : AnalyticWithinAt Complex f s x) (m : f x in slitPlane)
  proof: (analyticAt_clog m).comp_analyticWithinAt fa

中文:
定理 AnalyticWithinAt.clog
  条件: (fa : AnalyticWithinAt Complex f s x) (m : f x in slitPlane)
  证明: (analyticAt_clog m).comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_clog, comp_analyticWithinAt
-/
theorem AnalyticWithinAt.clog (fa : AnalyticWithinAt Complex f s x) (m : f x in slitPlane) :
    AnalyticWithinAt Complex (fun z => log (f z)) s x :=
  (analyticAt_clog m).comp_analyticWithinAt fa

/--
theorem `AnalyticOnNhd.clog` / 定理 `AnalyticOnNhd.clog`

English:
theorem AnalyticOnNhd.clog
  given: (fs : AnalyticOnNhd Complex f s) (m : forall z in s, f z in slitPlane)
  proof: fun z n => (analyticAt_clog (m z n)).comp (fs z n)

中文:
定理 AnalyticOnNhd.clog
  条件: (fs : AnalyticOnNhd Complex f s) (m : 对任意 z in s, f z in slitPlane)
  证明: fun z n => (analyticAt_clog (m z n)).comp (fs z n)

Depends on / 依赖: analyticAt_clog
-/
theorem AnalyticOnNhd.clog (fs : AnalyticOnNhd Complex f s) (m : forall z in s, f z in slitPlane) :
    AnalyticOnNhd Complex (fun z => log (f z)) s :=
  fun z n => (analyticAt_clog (m z n)).comp (fs z n)

/--
theorem `AnalyticOn.clog` / 定理 `AnalyticOn.clog`

English:
theorem AnalyticOn.clog
  given: (fs : AnalyticOn Complex f s) (m : forall z in s, f z in slitPlane)
  proof: fun z n => (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

中文:
定理 AnalyticOn.clog
  条件: (fs : AnalyticOn Complex f s) (m : 对任意 z in s, f z in slitPlane)
  证明: fun z n => (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

Depends on / 依赖: analyticAt_clog, analyticWithinAt, analyticWithinAt.comp
-/
theorem AnalyticOn.clog (fs : AnalyticOn Complex f s) (m : forall z in s, f z in slitPlane) :
    AnalyticOn Complex (fun z => log (f z)) s :=
  fun z n => (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

/--
theorem `AnalyticWithinAt.cpow` / 定理 `AnalyticWithinAt.cpow`

English:
theorem AnalyticWithinAt.cpow
  statement: (fa : AnalyticWithinAt Complex f s x) (ga : AnalyticWithinAt Complex g s x)
  proof: by
  have e : (fun z => f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z => exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact 

中文:
定理 AnalyticWithinAt.cpow
  结论: (fa : AnalyticWithinAt Complex f s x) (ga : AnalyticWithinAt Complex g s x)
  证明: by
  have e : (fun z => f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z => exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact 

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.congr_of_eventuallyEq_insert, congr_of_eventuallyEq_insert, continuousWithinAt_insert, cpow_def, eventually_ne, fa.clog, fa.continuousWithinAt_insert.eventually_ne, filter_upwards, if_false, insert, slitPlane_ne_zero
-/
theorem AnalyticWithinAt.cpow (fa : AnalyticWithinAt Complex f s x) (ga : AnalyticWithinAt Complex g s x)
    (m : f x in slitPlane) : AnalyticWithinAt Complex (fun z => f z ^ g z) s x := by
  have e : (fun z => f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z => exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact ((fa.clog m).mul ga).cexp

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
@[fun_prop]
/--
theorem `AnalyticAt.cpow` / 定理 `AnalyticAt.cpow`

English:
theorem AnalyticAt.cpow
  statement: (fa : AnalyticAt Complex f x) (ga : AnalyticAt Complex g x)
  proof: by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

中文:
定理 AnalyticAt.cpow
  结论: (fa : AnalyticAt Complex f x) (ga : AnalyticAt Complex g x)
  证明: by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

Depends on / 依赖: analyticWithinAt_univ, fa.cpow
-/
theorem AnalyticAt.cpow (fa : AnalyticAt Complex f x) (ga : AnalyticAt Complex g x)
    (m : f x in slitPlane) : AnalyticAt Complex (fun z => f z ^ g z) x := by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

/--
theorem `AnalyticOn.cpow` / 定理 `AnalyticOn.cpow`

English:
theorem AnalyticOn.cpow
  statement: (fs : AnalyticOn Complex f s) (gs : AnalyticOn Complex g s)
  proof: fun z n => (fs z n).cpow (gs z n) (m z n)

中文:
定理 AnalyticOn.cpow
  结论: (fs : AnalyticOn Complex f s) (gs : AnalyticOn Complex g s)
  证明: fun z n => (fs z n).cpow (gs z n) (m z n)
-/
theorem AnalyticOn.cpow (fs : AnalyticOn Complex f s) (gs : AnalyticOn Complex g s)
    (m : forall z in s, f z in slitPlane) : AnalyticOn Complex (fun z => f z ^ g z) s :=
  fun z n => (fs z n).cpow (gs z n) (m z n)

/--
theorem `AnalyticOnNhd.cpow` / 定理 `AnalyticOnNhd.cpow`

English:
theorem AnalyticOnNhd.cpow
  statement: (fs : AnalyticOnNhd Complex f s) (gs : AnalyticOnNhd Complex g s)
  proof: fun z n => (fs z n).cpow (gs z n) (m z n)

中文:
定理 AnalyticOnNhd.cpow
  结论: (fs : AnalyticOnNhd Complex f s) (gs : AnalyticOnNhd Complex g s)
  证明: fun z n => (fs z n).cpow (gs z n) (m z n)
-/
theorem AnalyticOnNhd.cpow (fs : AnalyticOnNhd Complex f s) (gs : AnalyticOnNhd Complex g s)
    (m : forall z in s, f z in slitPlane) : AnalyticOnNhd Complex (fun z => f z ^ g z) s :=
  fun z n => (fs z n).cpow (gs z n) (m z n)

section ReOfReal

variable {f : Complex -> Complex} {s : Set Real} {x : Real}

@[fun_prop]
/--
lemma `AnalyticAt.re_ofReal` / 引理 `AnalyticAt.re_ofReal`

English:
lemma AnalyticAt.re_ofReal
  given: (hf : AnalyticAt Complex f x)
  proof: (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]

中文:
引理 AnalyticAt.re_ofReal
  条件: (hf : AnalyticAt Complex f x)
  证明: (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]

Depends on / 依赖: Complex.ofRealCLM.analyticAt, Complex.reCLM.analyticAt, analyticAt, hf.restrictScalars.comp, ofRealCLM, restrictScalars
-/
lemma AnalyticAt.re_ofReal (hf : AnalyticAt Complex f x) :
    AnalyticAt Real (fun x : Real => (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]
/--
lemma `AnalyticAt.im_ofReal` / 引理 `AnalyticAt.im_ofReal`

English:
lemma AnalyticAt.im_ofReal
  given: (hf : AnalyticAt Complex f x)
  proof: (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

中文:
引理 AnalyticAt.im_ofReal
  条件: (hf : AnalyticAt Complex f x)
  证明: (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

Depends on / 依赖: Complex.imCLM.analyticAt, Complex.ofRealCLM.analyticAt, analyticAt, hf.restrictScalars.comp, ofRealCLM, restrictScalars
-/
lemma AnalyticAt.im_ofReal (hf : AnalyticAt Complex f x) :
    AnalyticAt Real (fun x : Real => (f x).im) x :=
  (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

/--
lemma `AnalyticWithinAt.re_ofReal` / 引理 `AnalyticWithinAt.re_ofReal`

English:
lemma AnalyticWithinAt.re_ofReal
  given: (hf : AnalyticWithinAt Complex f (ofReal '' s) x)
  proof: ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

中文:
引理 AnalyticWithinAt.re_ofReal
  条件: (hf : AnalyticWithinAt Complex f (of实数 '' s) x)
  证明: ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.ofRealCLM.analyticWithinAt, Complex.reCLM.analyticWithinAt, analyticWithinAt, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticWithinAt.re_ofReal (hf : AnalyticWithinAt Complex f (ofReal '' s) x) :
    AnalyticWithinAt Real (fun x : Real => (f x).re) s x :=
  ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

/--
lemma `AnalyticWithinAt.im_ofReal` / 引理 `AnalyticWithinAt.im_ofReal`

English:
lemma AnalyticWithinAt.im_ofReal
  given: (hf : AnalyticWithinAt Complex f (ofReal '' s) x)
  proof: ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

中文:
引理 AnalyticWithinAt.im_ofReal
  条件: (hf : AnalyticWithinAt Complex f (of实数 '' s) x)
  证明: ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.imCLM.analyticWithinAt, Complex.ofRealCLM.analyticWithinAt, analyticWithinAt, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticWithinAt.im_ofReal (hf : AnalyticWithinAt Complex f (ofReal '' s) x) :
    AnalyticWithinAt Real (fun x : Real => (f x).im) s x :=
  ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

/--
lemma `AnalyticOn.re_ofReal` / 引理 `AnalyticOn.re_ofReal`

English:
lemma AnalyticOn.re_ofReal
  given: (hf : AnalyticOn Complex f (ofReal '' s))
  proof: ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

中文:
引理 AnalyticOn.re_ofReal
  条件: (hf : AnalyticOn Complex f (of实数 '' s))
  证明: ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.ofRealCLM.analyticOn, Complex.reCLM.analyticOn, analyticOn, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticOn.re_ofReal (hf : AnalyticOn Complex f (ofReal '' s)) :
    AnalyticOn Real (fun x : Real => (f x).re) s :=
  ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

/--
lemma `AnalyticOn.im_ofReal` / 引理 `AnalyticOn.im_ofReal`

English:
lemma AnalyticOn.im_ofReal
  given: (hf : AnalyticOn Complex f (ofReal '' s))
  proof: ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

中文:
引理 AnalyticOn.im_ofReal
  条件: (hf : AnalyticOn Complex f (of实数 '' s))
  证明: ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.imCLM.analyticOn, Complex.ofRealCLM.analyticOn, analyticOn, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticOn.im_ofReal (hf : AnalyticOn Complex f (ofReal '' s)) :
    AnalyticOn Real (fun x : Real => (f x).im) s :=
  ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

/--
lemma `AnalyticOnNhd.re_ofReal` / 引理 `AnalyticOnNhd.re_ofReal`

English:
lemma AnalyticOnNhd.re_ofReal
  given: (hf : AnalyticOnNhd Complex f (ofReal '' s))
  proof: ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

中文:
引理 AnalyticOnNhd.re_ofReal
  条件: (hf : AnalyticOnNhd Complex f (of实数 '' s))
  证明: ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.ofRealCLM.analyticOnNhd, Complex.reCLM.analyticOnNhd, analyticOnNhd, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticOnNhd.re_ofReal (hf : AnalyticOnNhd Complex f (ofReal '' s)) :
    AnalyticOnNhd Real (fun x : Real => (f x).re) s :=
  ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

/--
lemma `AnalyticOnNhd.im_ofReal` / 引理 `AnalyticOnNhd.im_ofReal`

English:
lemma AnalyticOnNhd.im_ofReal
  given: (hf : AnalyticOnNhd Complex f (ofReal '' s))
  proof: ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

中文:
引理 AnalyticOnNhd.im_ofReal
  条件: (hf : AnalyticOnNhd Complex f (of实数 '' s))
  证明: ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

Depends on / 依赖: Complex.imCLM.analyticOnNhd, Complex.ofRealCLM.analyticOnNhd, analyticOnNhd, hf.restrictScalars, mapsTo_image, ofReal, ofRealCLM, restrictScalars
-/
lemma AnalyticOnNhd.im_ofReal (hf : AnalyticOnNhd Complex f (ofReal '' s)) :
    AnalyticOnNhd Real (fun x : Real => (f x).im) s :=
  ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

end ReOfReal

section Real

variable {f : Real -> Real} {s : Set Real} {x : Real}

@[fun_prop]
/--
lemma `analyticAt_log` / 引理 `analyticAt_log`

English:
lemma analyticAt_log
  given: (hx : 0 < x)
  statement: AnalyticAt Real Real.log x
  proof: by
  have : Real.log = fun x : Real => (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
refine AnalyticAt.re_ofReal analyticAt_clog ?_
  simp [hx]

中文:
引理 analyticAt_log
  条件: (hx : 0 < x)
  结论: AnalyticAt 实数 实数.log x
  证明: by
  have : Real.log = fun x : Real => (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
refine AnalyticAt.re_ofReal analyticAt_clog ?_
  simp [hx]

Depends on / 依赖: AnalyticAt, AnalyticAt.re_ofReal, Complex.log, Complex.log_ofReal_re, Real.log, analyticAt_clog, log_ofReal_re, re_ofReal
-/
lemma analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x := by
  have : Real.log = fun x : Real => (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
refine AnalyticAt.re_ofReal analyticAt_clog ?_
  simp [hx]

/--
lemma `analyticOnNhd_log` / 引理 `analyticOnNhd_log`

English:
lemma analyticOnNhd_log
  statement: AnalyticOnNhd Real Real.log (Set.Ioi 0)
  proof: fun _ hx => analyticAt_log hx

中文:
引理 analyticOnNhd_log
  结论: AnalyticOnNhd 实数 实数.log (Set.Ioi 0)
  证明: fun _ hx => analyticAt_log hx

Depends on / 依赖: analyticAt_log
-/
lemma analyticOnNhd_log : AnalyticOnNhd Real Real.log (Set.Ioi 0) := fun _ hx => analyticAt_log hx

/--
lemma `analyticOn_log` / 引理 `analyticOn_log`

English:
lemma analyticOn_log
  statement: AnalyticOn Real Real.log (Set.Ioi 0)
  proof: analyticOnNhd_log.analyticOn

@[fun_prop]

中文:
引理 analyticOn_log
  结论: AnalyticOn 实数 实数.log (Set.Ioi 0)
  证明: analyticOnNhd_log.analyticOn

@[fun_prop]

Depends on / 依赖: analyticOn, analyticOnNhd_log, analyticOnNhd_log.analyticOn
-/
lemma analyticOn_log : AnalyticOn Real Real.log (Set.Ioi 0) := analyticOnNhd_log.analyticOn

@[fun_prop]
/--
lemma `AnalyticAt.log` / 引理 `AnalyticAt.log`

English:
lemma AnalyticAt.log
  given: (fa : AnalyticAt Real f x) (m : 0 < f x)
  proof: (analyticAt_log m).comp fa

中文:
引理 AnalyticAt.log
  条件: (fa : AnalyticAt 实数 f x) (m : 0 < f x)
  证明: (analyticAt_log m).comp fa

Depends on / 依赖: analyticAt_log
-/
lemma AnalyticAt.log (fa : AnalyticAt Real f x) (m : 0 < f x) :
    AnalyticAt Real (fun z => Real.log (f z)) x :=
  (analyticAt_log m).comp fa

/--
lemma `AnalyticWithinAt.log` / 引理 `AnalyticWithinAt.log`

English:
lemma AnalyticWithinAt.log
  given: (fa : AnalyticWithinAt Real f s x) (m : 0 < f x)
  proof: (analyticAt_log m).comp_analyticWithinAt fa

中文:
引理 AnalyticWithinAt.log
  条件: (fa : AnalyticWithinAt 实数 f s x) (m : 0 < f x)
  证明: (analyticAt_log m).comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_log, comp_analyticWithinAt
-/
lemma AnalyticWithinAt.log (fa : AnalyticWithinAt Real f s x) (m : 0 < f x) :
    AnalyticWithinAt Real (fun z => Real.log (f z)) s x :=
  (analyticAt_log m).comp_analyticWithinAt fa

/--
lemma `AnalyticOnNhd.log` / 引理 `AnalyticOnNhd.log`

English:
lemma AnalyticOnNhd.log
  given: (fs : AnalyticOnNhd Real f s) (m : forall x in s, 0 < f x)
  proof: fun z n => (analyticAt_log (m z n)).comp (fs z n)

中文:
引理 AnalyticOnNhd.log
  条件: (fs : AnalyticOnNhd 实数 f s) (m : 对任意 x in s, 0 < f x)
  证明: fun z n => (analyticAt_log (m z n)).comp (fs z n)

Depends on / 依赖: analyticAt_log
-/
lemma AnalyticOnNhd.log (fs : AnalyticOnNhd Real f s) (m : forall x in s, 0 < f x) :
    AnalyticOnNhd Real (fun z => Real.log (f z)) s :=
  fun z n => (analyticAt_log (m z n)).comp (fs z n)

/--
lemma `AnalyticOn.log` / 引理 `AnalyticOn.log`

English:
lemma AnalyticOn.log
  given: (fs : AnalyticOn Real f s) (m : forall x in s, 0 < f x)
  proof: fun z n => (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m

中文:
引理 AnalyticOn.log
  条件: (fs : AnalyticOn 实数 f s) (m : 对任意 x in s, 0 < f x)
  证明: fun z n => (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m

Depends on / 依赖: analyticAt_log, analyticWithinAt, analyticWithinAt.comp
-/
lemma AnalyticOn.log (fs : AnalyticOn Real f s) (m : forall x in s, 0 < f x) :
    AnalyticOn Real (fun z => Real.log (f z)) s :=
  fun z n => (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m

/--
theorem `iteratedDeriv_succ_log` / 定理 `iteratedDeriv_succ_log`

English:
theorem iteratedDeriv_succ_log
  given: {n : Nat} {x : Complex} (hx : x in slitPlane)
  proof: by
  have h_eq : deriv log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [isOpen_slitPlane.mem_nhds hx] with y hy
    simp [Complex.deriv_log hy]
  rw [iteratedDeriv_succ']; rw [h_eq.iteratedDeriv_eq]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_inv]
  grind

中文:
定理 iteratedDeriv_succ_log
  条件: {n : 自然数} {x : Complex} (hx : x in slitPlane)
  证明: by
  have h_eq : deriv log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [isOpen_slitPlane.mem_nhds hx] with y hy
    simp [Complex.deriv_log hy]
  rw [iteratedDeriv_succ']; rw [h_eq.iteratedDeriv_eq]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_inv]
  grind

Depends on / 依赖: Complex.deriv_log, Inv.inv, deriv_log, filter_upwards, h_eq, h_eq.iteratedDeriv_eq, isOpen_slitPlane, isOpen_slitPlane.mem_nhds, iter_deriv_inv, iteratedDeriv_eq, iteratedDeriv_eq_iterate, iteratedDeriv_succ, mem_nhds
-/
theorem iteratedDeriv_succ_log {n : Nat} {x : Complex} (hx : x in slitPlane) :
    iteratedDeriv (n + 1) log x = (-1 : Complex) ^ n * n.factorial * x ^ (-(n : Int) - 1) := by
  have h_eq : deriv log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [isOpen_slitPlane.mem_nhds hx] with y hy
    simp [Complex.deriv_log hy]
  rw [iteratedDeriv_succ']; rw [h_eq.iteratedDeriv_eq]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_inv]
  grind

/--
theorem `hasFPowerSeriesAt_clog_one` / 定理 `hasFPowerSeriesAt_clog_one`

English:
theorem hasFPowerSeriesAt_clog_one
  proof: by
  suffices ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) =
      FormalMultilinearSeries.ofScalars Complex (fun n => iteratedDeriv n log 1 / (n.factorial : Complex))) by
    convert! AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analytic

中文:
定理 hasFPowerSeriesAt_clog_one
  证明: by
  suffices ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) =
      FormalMultilinearSeries.ofScalars Complex (fun n => iteratedDeriv n log 1 / (n.factorial : Complex))) by
    convert! AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analytic

Depends on / 依赖: AnalyticAt, AnalyticAt.hasFPowerSeriesAt, Finset, Finset.prod_const_one, FormalMultilinearSeries, FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars, FormalMultilinearSeries.ofScalars, analyticAt_clog, apply_eq_prod_smul_coeff, coeff_ofScalars, convert, factorial, hasFPowerSeriesAt, infer_instance, iteratedDeriv, iteratedDeriv_, n.factorial, ofScalars, one_mul
-/
theorem hasFPowerSeriesAt_clog_one :
    HasFPowerSeriesAt log (.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) 1 := by
  suffices ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) =
      FormalMultilinearSeries.ofScalars Complex (fun n => iteratedDeriv n log 1 / (n.factorial : Complex))) by
    convert! AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analyticAt_clog (by simp)
  ext n
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const_one,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, one_mul]
  obtain _ | n := n
  · simp
  simp [iteratedDeriv_succ_log one_mem_slitPlane, Nat.factorial_succ, pow_succ]
  field_simp [show n.factorial != 0 by positivity]

/--
theorem `hasFPowerSeriesAt_clog_one_add` / 定理 `hasFPowerSeriesAt_clog_one_add`

English:
theorem hasFPowerSeriesAt_clog_one_add
  proof: by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_clog_one (-1) using 3 <;> ring

中文:
定理 hasFPowerSeriesAt_clog_one_add
  证明: by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_clog_one (-1) using 3 <;> ring

Depends on / 依赖: HasFPowerSeriesAt, HasFPowerSeriesAt.comp_sub, comp_sub, convert, hasFPowerSeriesAt_clog_one
-/
theorem hasFPowerSeriesAt_clog_one_add :
    HasFPowerSeriesAt (fun x => log (1 + x)) (.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_clog_one (-1) using 3 <;> ring

/--
theorem `hasFPowerSeriesAt_log_one` / 定理 `hasFPowerSeriesAt_log_one`

English:
theorem hasFPowerSeriesAt_log_one
  proof: by
  obtain ⟨r, hp⟩ := hasFPowerSeriesAt_clog_one
  have : HasFPowerSeriesOnBall log
      ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)).restrictScalars Real)
      (ofRealCLM 1) r := by
    simpa using hp.restrictScalars
  convert ((reCLM.comp_hasFPowerSeriesOnBall

中文:
定理 hasFPowerSeriesAt_log_one
  证明: by
  obtain ⟨r, hp⟩ := hasFPowerSeriesAt_clog_one
  have : HasFPowerSeriesOnBall log
      ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)).restrictScalars Real)
      (ofRealCLM 1) r := by
    simpa using hp.restrictScalars
  convert ((reCLM.comp_hasFPowerSeriesOnBall

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.compFormalMultilinearSeries_apply, FormalMultilinearSeries, FormalMultilinearSeries.ofScalars, Function, Function.co, HasFPowerSeriesOnBall, compContinuousLinearMap, compContinuousMultilinearMap_coe, compFormalMultilinearSeries_apply, comp_hasFPowerSeriesOnBall, convert, hasFPowerSeriesAt, hasFPowerSeriesAt_clog_one, hp.restrictScalars, log_ofReal_re, ofRealCLM, ofScalars, reCLM.comp_hasFPowerSeriesOnBall
-/
theorem hasFPowerSeriesAt_log_one :
    HasFPowerSeriesAt Real.log (.ofScalars Real (fun n => -(-1 : Real) ^ n / n)) 1 := by
  obtain ⟨r, hp⟩ := hasFPowerSeriesAt_clog_one
  have : HasFPowerSeriesOnBall log
      ((FormalMultilinearSeries.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)).restrictScalars Real)
      (ofRealCLM 1) r := by
    simpa using hp.restrictScalars
  convert ((reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr
    (fun x _ => log_ofReal_re x)).hasFPowerSeriesAt
  ext n
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  simp
  norm_cast

/--
theorem `hasFPowerSeriesAt_log_one_add` / 定理 `hasFPowerSeriesAt_log_one_add`

English:
theorem hasFPowerSeriesAt_log_one_add
  proof: by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_log_one (-1) using 3 <;> ring

中文:
定理 hasFPowerSeriesAt_log_one_add
  证明: by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_log_one (-1) using 3 <;> ring

Depends on / 依赖: HasFPowerSeriesAt, HasFPowerSeriesAt.comp_sub, comp_sub, convert, hasFPowerSeriesAt_log_one
-/
theorem hasFPowerSeriesAt_log_one_add :
    HasFPowerSeriesAt (fun x => Real.log (1 + x)) (.ofScalars Real (fun n => -(-1 : Real) ^ n / n)) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_log_one (-1) using 3 <;> ring

end Real
