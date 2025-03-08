variables (A : Type)
variables (RR : A → A → Prop)
variables (PP : A → Prop)  -- 声明 PP 是 A 上的一个谓词



theorem ex6q02 : ∀ x y : A, x = y → RR x y → RR x x :=
begin
  -- **第一步：引入变量和假设**
  assume x y,       -- 1. 让 x 和 y 是 A 的任意元素
  assume hxy,       -- 2. 假设 x = y
  assume hrxy,      -- 3. 假设 RR x y 成立

  -- **第二步：使用 `cases` 替换 `y` 为 `x`**
  cases hxy,        -- 让 `y` 在所有地方替换成 `x`
  
  -- **第三步：目标变成 `RR x x`，直接使用 `hrxy`**
  exact hrxy,       -- 直接完成证明
end







theorem ex6q04 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin
  -- **第一步：引入变量和假设**
  assume x y z,  -- 让 x, y, z 是 A 中的任意元素
  assume hxy,    -- 假设 x ≠ y，即 ¬(x = y)

  -- **第二步：使用经典逻辑 (排中律) 进行分类讨论**
  cases classical.em (x = z) with hxz hxz,  -- `hxz : x = z` 或 `hxz : x ≠ z`
  
  -- **情况 1: 假设 `x = z`，需要推出 `y ≠ z`**
  right, -- 选择 `∨` 的右分支，目标是证明 `y ≠ z`
  assume hyz, -- 假设 `y = z`，尝试推导矛盾

  -- **第三步：手动推导 `x = y`**
  cases hxz,   -- 用 `hxz : x = z` 直接替换 x 为 z
  cases hyz,   -- 用 `hyz : y = z` 直接替换 y 为 z

  -- **推出矛盾**
  contradiction, -- 但 `hxy : x ≠ y`，所以 `x = y` 矛盾！

  -- **情况 2: 假设 `x ≠ z`，直接推出结论**
  left,  -- 选择 `∨` 的左分支，目标是证明 `x ≠ z`
  exact hxz, -- 直接使用 `hxz : x ≠ z`
end







theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  -- **第一步：引入假设**
  assume h,  -- 设 h : ¬ (∀ x : A, PP x)，即 "不是所有 x 都满足 PP x"

  -- **第二步：使用排中律进行分析**
  cases classical.em (∃ x : A, ¬ PP x) with hex hex,
  
  -- **情况 1：假设 ∃ x : A, ¬ PP x 成立**
  exact hex,  -- 直接返回 hex 作为结论

  -- **情况 2：假设 ¬ ∃ x : A, ¬ PP x**
  -- 这意味着 "所有 x 都满足 PP x"
  have hforall : ∀ x : A, PP x,  -- 设 ∀ x, PP x
  assume x,
  by_contradiction hnp,  -- 假设 PP x 不成立
  apply hex,             -- 但 hex 是 ¬ ∃ x, ¬ PP x
  existsi x,             -- 但是我们确实找到了一个这样的 x，使 PP x 不成立
  exact hnp,             -- 这与 hex 矛盾！

  -- **推出矛盾**
  contradiction,  -- 但 h : ¬ (∀ x, PP x)，矛盾！
end
