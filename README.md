# LeanGeo (paper to be published)
______________________________________________________________________

## running LeanGeo-Bench eval

To launch the server, clone and cd into the LeanGeo repository and then run: 
```
cp .env.template .env
docker compose up -d
```

## Quick Links

1. [Requirements](#requirements)  
1. [Building](#building)
1. [The Formal System E](#the-formal-system-e)
1. [LeanEuclid](#leaneuclid)
    1. [Euclid's *Elements*](#euclids-elements)
    1. [UniGeo](#unigeo)
1. [Evaluating on LeanGeo-Bench](#evaluating-on-leangeo-bench)
1. [Experiments](#experiments)
1. [Acknowledgements](#acknowledgements)



## Requirements

It is recommended that you run this repo on linux (if you are on windows you can use wsl). 

You will need to install the following linux packages: 
```
clang
libc++-dev
cvc5
libcvc5-dev
```

Additionally, your `C` and `CXX` compilers both need to be set to `clang`. Which can be done using the following command
```
export CC=clang
export CXX=clang++
```

## Building

Take the following steps to build the Lean project:

1. Run `lake run cvc5/downloadRelease` to install the latest copy of `cvc5`
2. Run `lake script run check` to check if the requirements are satisfied.
3. Run `lake exe cache get` to download the [mathlib](https://github.com/leanprover-community/mathlib4) cache
4. Run `lake build` to compile the formal system E
5. Open a file for Euclid's *Elements* in VS Code, e.g., [Book/Prop01.lean](Book/Prop01.lean). You should expect to see:

![Elements Prop1](https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/Elements_prop1.png)


Optionally, you can:

1. Run `lake -R -Kenv=dev build SystemE:docs` to build the documentation
1. View the auto-generated documentation locally at ./lake/build/doc, e.g., using `python -mhttp.server`

If you have problems building the project, [Dockerfile](./Dockerfile) and [scripts/build.sh](./scripts/build.sh) may serve as useful references.


## The Formal System E

E is a formal system introduced by [Avigad et al., 2009](https://arxiv.org/abs/0810.4315) for faithfully formalizing the proofs in Euclid’s *Elements*, including the use of diagrammatic reasoning. It defines a language for expressing basic objects in 2D Euclidean geometry (points, lines, circles, etc.), as well as the form of theorems and proofs. We implement the formal system E in Lean and use SMT solvers to perform diagrammatic reasoning automatically and implicitly. Details of our implementation can be found [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/SystemE) and in the auto-generated documentation.



## LeanGeo-Bench
We introduce LeanGeo-Bench, the first benchmark specifically designed for the formal proof of plane geometry theorems. As detailed in Table \ref{sample-table}, LeanGeo-Bench comprises 123 problems sourced from theorem library, textbooks, synthetic generation and competitions like the IMO, covering a wide spectrum of difficulty.


### Euclid's *Elements*

We manually formalized the first book of Euclid's *Elements*, using an [open-source LaTex version](https://github.com/rfitzp/Elements). The formalized theorems and proofs can be found [here](./Book). Thanks to E and automatic diagrammatic reasoning, our formalized proofs are "faithful" in the sense that they correspond very closely to Euclid's original proofs. To our knowledge, this is the first time Euclid's *Elements* has been faithfully formalized in a proof assistant such as Lean, and our formalization has uncovered errors in Euclid's proofs (Appendix B of our paper).

For example, below is our formalization of Euclid's first proposition in Book I, which states you can construct an equilateral triangle given two distinct points:

<img width="444" alt="image" src="https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/Elements_prop1_Euclid.png">

Our formalized theorem and proof in [Book/Prop01.lean](https://github.com/loganrjmurphy/LeanEuclid/blob/master/Book/Prop01.lean):

```lean
theorem proposition_1 :
∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
    ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
    euclid_intros
    euclid_apply circle_from_points a b as BCD
    euclid_apply circle_from_points b a as ACE
    euclid_apply intersection_circles BCD ACE as c
    euclid_apply point_on_circle_onlyif a b c BCD
    euclid_apply point_on_circle_onlyif b a c ACE
    use c
    euclid_finish
```

## Evaluating on LeanGeo-Bench

### Evaluation Framwork

We use the evaluation method provided by CombiBench. See https://github.com/MoonshotAI/CombiBench/tree/master for details.

### Setup Environment

You need to follow these steps to quickly install the required packages.

First, install the lean server on a device with sufficient CPU and memory (Recommended: [TODO]).

~~~
git clone https://github.com/project-numina/kimina-lean-server.git
cd kimina-lean-server
git checkout leangeo
~~~

Second, download Combibench on any device.

~~~
git clone https://github.com/MoonshotAI/CombiBench.git
cd CombiBench
~~~


### Setup a Lean Server

Follow https://github.com/project-numina/kimina-lean-server/tree/leangeo to configure a lean server and get a custom url and API_KEY.

You can use the following instructions to build a lean server quickly.
~~~
cp .env.template .env
docker compose up -d
~~~

You can also change the port number of lean server in the `compose.yaml` file to align with the port number required by `CombiBench/evaluation`.

### Setup a LLM API Key

We support API interfaces such as OpenAI, Antropic, TogetherAI, and Google GenerativeAI.

### Configuration

Refer to https://github.com/MoonshotAI/CombiBench/blob/master/evaluation/config/geometry_template.json5 to configure the dataset, lean server, llm server, generation parameters, prompt, and parallel parameters.

You can also add custom prompts under the `CombiBench/evaluation/config/extra_prompt` and configure the path in the `prompt_template` argument within the config file. 

### Run Evaluation

To run evaluation on LeanGeo-Bench:

```
python evaluation/cli.py online-one-stage -c evaluation/config/geometry_template.json5
```

## Experiments


## Acknowledgements

* Our SystemE implementation is heavily inspired by LeanEuclid.
* However, unlike LeanEuclid we use LeanSMT's builtin translator, caching the SystemE axioms for speed purpose.

## Contributions

We would like this to be a community driven repo. Specifically the following areas require development

1. Expanding the theorem library.
2. Getting proof reconstruction to work for the `esmt` tactic.
3. Improve axiom caching: currently the `@[euclid]` attribute requires that axioms imports are chained linearly (eg `superposition` imports `metric` which imports `diagrammatic`). If someone could get the caching to work using something like [DiscrTree](https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/DiscrTreeTypes.html#Lean.Meta.DiscrTree) that would be greatly appreciated.
4. Mathlib comptability: in the `to415_mathlib` branch we define all SystemE primitives and axioms in terms of complex numbers. Sorry filling for SystemE axioms would be greatly appreciated. The smt solver interface is also broken on that branch so if any could implement monomorphization that would be great too.