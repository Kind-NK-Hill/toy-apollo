# Chapter 1/2 Cross-Chapter Dependency Rules

## Scope

This note records the Chapter 1 and Chapter 2 cross-chapter dependency rule used
before opening local Phase 2 work for those chapters.

## 判定标准

只用这三条：

1. 显式引用：task A 文本直接点名 B。
2. 表述不可缺：task A 本身必须用到对应 task B。
3. 不做传递提升：如果 task A 其实是通过本章的其他 task 或者比 task B 更靠后的 task C
   间接继承这些概念，就不补 task B。

## Operational Interpretation

- A bibliographic citation is not automatically a task dependency.
- A forward-looking remark such as "this is a preliminary idea of ..." is not
  automatically a task dependency.
- If a task can be formalized from its own statement plus same-chapter prior
  tasks, do not add an extra cross-chapter dependency.

## Current Chapter 1/2 Decision

- Chapter 1 should not depend on later chapters through bibliographic references
  alone.
- Chapter 2 may depend on Chapter 1 only when the three rules above are
  satisfied.
- Do not promote indirect or transitive dependencies into explicit
  cross-chapter imports.
