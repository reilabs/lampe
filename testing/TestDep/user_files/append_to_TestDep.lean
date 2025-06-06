
theorem t1 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t2 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».hello_git_dep.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-0.0.0».hello_git_dep]
  steps []
  subst_vars
  rfl

theorem t3 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-v1" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t4 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».hello_git_dep_v1.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-v1" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».hello_git_dep_v1]
  steps []
  subst_vars
  rfl

theorem t5 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-v2" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t6 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».hello_git_dep_v2.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-v2" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«GitDep-2.0.0».hello_git_dep_v2]
  steps []
  subst_vars
  rfl

theorem t11 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t12 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».hello_local_dep.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-0.0.0».hello_local_dep]
  steps []
  subst_vars
  rfl

theorem t13 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-v1" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t14 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».hello_local_dep_v1.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-v1" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-1.0.0».hello_local_dep_v1]
  steps []
  subst_vars
  rfl

theorem t15 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-v2" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».hello]
  steps []
  subst_vars
  rfl

theorem t16 {lp}: STHoare lp «TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».env (⟦⟧)
    («TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».hello_local_dep_v2.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-v2" := by
  enter_decl
  simp only [«TestDep-0.0.0».Extracted.Dependencies.«LocalDep-2.0.0».hello_local_dep_v2]
  steps []
  subst_vars
  rfl


theorem t21 {lp}: STHoare lp «GitDepWithLampe-0.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-0.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe" := by
  enter_decl
  simp only [«GitDepWithLampe-0.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t22 {lp}: STHoare lp «GitDepWithLampe-0.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-0.0.0».Extracted.hello_git_dep_with_lampe.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe" := by
  enter_decl
  simp only [«GitDepWithLampe-0.0.0».Extracted.hello_git_dep_with_lampe]
  steps []
  subst_vars
  rfl

theorem t23 {lp}: STHoare lp «GitDepWithLampe-1.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-1.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe-v1" := by
  enter_decl
  simp only [«GitDepWithLampe-1.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t24 {lp}: STHoare lp «GitDepWithLampe-1.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-1.0.0».Extracted.hello_git_dep_with_lampe_v1.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe-v1" := by
  enter_decl
  simp only [«GitDepWithLampe-1.0.0».Extracted.hello_git_dep_with_lampe_v1]
  steps []
  subst_vars
  rfl

theorem t25 {lp}: STHoare lp «GitDepWithLampe-2.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-2.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe-v2" := by
  enter_decl
  simp only [«GitDepWithLampe-2.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t26 {lp}: STHoare lp «GitDepWithLampe-2.0.0».Extracted.env (⟦⟧)
    («GitDepWithLampe-2.0.0».Extracted.hello_git_dep_with_lampe_v2.call h![] h![])
      fun output => (String.mk output.toList) = "hello-git-dep-with-lampe-v2" := by
  enter_decl
  simp only [«GitDepWithLampe-2.0.0».Extracted.hello_git_dep_with_lampe_v2]
  steps []
  subst_vars
  rfl


theorem t31 {lp}: STHoare lp «LocalDepWithLampe-0.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-0.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe" := by
  enter_decl
  simp only [«LocalDepWithLampe-0.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t32 {lp}: STHoare lp «LocalDepWithLampe-0.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-0.0.0».Extracted.hello_local_dep_with_lampe.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe" := by
  enter_decl
  simp only [«LocalDepWithLampe-0.0.0».Extracted.hello_local_dep_with_lampe]
  steps []
  subst_vars
  rfl

theorem t33 {lp}: STHoare lp «LocalDepWithLampe-1.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-1.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe-v1" := by
  enter_decl
  simp only [«LocalDepWithLampe-1.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t34 {lp}: STHoare lp «LocalDepWithLampe-1.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-1.0.0».Extracted.hello_local_dep_with_lampe_v1.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe-v1" := by
  enter_decl
  simp only [«LocalDepWithLampe-1.0.0».Extracted.hello_local_dep_with_lampe_v1]
  steps []
  subst_vars
  rfl

theorem t35 {lp}: STHoare lp «LocalDepWithLampe-2.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-2.0.0».Extracted.hello.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe-v2" := by
  enter_decl
  simp only [«LocalDepWithLampe-2.0.0».Extracted.hello]
  steps []
  subst_vars
  rfl

theorem t36 {lp}: STHoare lp «LocalDepWithLampe-2.0.0».Extracted.env (⟦⟧)
    («LocalDepWithLampe-2.0.0».Extracted.hello_local_dep_with_lampe_v2.call h![] h![])
      fun output => (String.mk output.toList) = "hello-local-dep-with-lampe-v2" := by
  enter_decl
  simp only [«LocalDepWithLampe-2.0.0».Extracted.hello_local_dep_with_lampe_v2]
  steps []
  subst_vars
  rfl
