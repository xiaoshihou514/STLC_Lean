# 主类型推导的形式化证明

本项目是对简单类型λ演算主类型推导算法的完整形式化验证，使用Lean 4定理证明器实现。项目包含：

- STLC 定义及类型检查器；
- 主类型推导算法的 Lean 4 实现；
- 利用 Lean 依赖类型系统对罗宾逊合一算法终止性的证明；
- 类型推导算法的正确性证明。

具体请阅读[报告：STLC类型推导之证明](./doc/STLC类型推导之证明.pdf)。

Lean文档：https://xiaoshihou514.github.io/STLC_Lean/docs/STLCLean/proof.html

_Formal Proof of Principal Type Inference_

This project provides a complete formal verification of a principal type inference algorithm for the simply typed lambda calculus (STLC), implemented using the Lean 4 theorem prover. The project includes:

- Definition of STLC and a type checker;
- Implementation of the principal type inference algorithm in Lean 4;
- A proof of termination for Robinson's unification algorithm using Lean's dependent type system;
- A proof of correctness for the type inference algorithm.

For details, please read the report [part 1](./doc/Pars_Prima.pdf), [part 2](./doc/Pars_Secunda.pdf).
