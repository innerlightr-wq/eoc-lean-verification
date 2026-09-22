"""Domain-mismatch guard, applied BEFORE detailed retrieval.

Gate 7. Motivated by a concrete MVP failure: the question

    "Does the Riemann hypothesis imply anything here?"

returned the Tao-mixing and Curry nodes, ranked confidently, on the strength of
the single shared word "hypothesis". A reader would conclude the repository has
something to say about RH. It does not.

There are two independent causes and this module fixes both:

1. *Named external subject.* The query is about a body of mathematics the
   repository has never touched. Handled by an explicit, auditable entity list.
   No ontology, no embeddings -- if a term is not on the list it is not claimed
   to be recognised.

2. *Generic-word matching.* "hypothesis", "conjecture", "theorem", "problem"
   are load-bearing in almost every mathematical sentence and carry no topical
   information. They inflated relevance for free. Handled by GENERIC_TERMS,
   which are excluded from relevance scoring for every query, in-domain ones
   included. This fix is independent of the entity list, so a *new* external
   subject nobody listed still cannot win on a generic word alone.

Transfer questions are explicitly protected. "Could a technique from the
Riemann hypothesis literature help the EOC arithmetic bottleneck?" is a
legitimate question and must not be refused; it is passed through and labelled,
with the caveat that any match is an analogy the reader must justify.
"""
from __future__ import annotations

import re

# Mathematics the repository does not study. Deliberately short and explicit:
# each entry is a phrase a reader can check. Multi-word entries are matched as
# phrases so "elliptic" alone (or "curve", which EOC does use geometrically)
# does not trip the guard.
EXTERNAL_SUBJECTS: dict[str, tuple[str, ...]] = {
    "Riemann hypothesis": ("riemann hypothesis", "riemann zeta", "zeta zeros",
                           "critical line", "nontrivial zeros"),
    "Birch and Swinnerton-Dyer": ("birch and swinnerton", "swinnerton-dyer", "bsd conjecture"),
    "Navier-Stokes": ("navier-stokes", "navier stokes"),
    "Yang-Mills": ("yang-mills", "yang mills", "mass gap"),
    "Hodge conjecture": ("hodge conjecture",),
    "Poincare conjecture": ("poincare conjecture", "poincaré conjecture", "ricci flow"),
    "P versus NP": ("p versus np", "p vs np", "np-complete", "np complete"),
    "modular forms": ("modular form", "modular forms", "eisenstein series", "hecke operator"),
    "elliptic curves": ("elliptic curve", "elliptic curves", "mordell-weil", "neron-severi"),
    "Fermat's Last Theorem": ("fermat's last", "fermats last"),
    "twin primes": ("twin prime", "twin primes"),
    "Goldbach": ("goldbach",),
    "Langlands": ("langlands",),
    "K3 surfaces": ("k3 surface", "k3 surfaces"),
    "class field theory": ("class field theory", "galois representation"),
    "knot theory": ("knot theory", "jones polynomial"),
    "machine learning": ("neural network", "transformer model", "gradient descent",
                         "large language model"),
}

# Ordinary English stopwords. Lives here rather than in retrieve.py because the
# domain vocabulary must exclude them too: semantic-node titles and summaries are
# English prose, so without this "the" enters the repository vocabulary and every
# query looks topical. That is not hypothetical -- it let the Riemann-hypothesis
# query past the guard as a "transfer request" on the strength of the word "the".
STOPWORDS = {
    "the", "a", "an", "of", "to", "in", "is", "are", "can", "does", "do", "for",
    "and", "or", "on", "by", "with", "what", "which", "that", "this", "it", "as",
    "be", "from", "at", "any", "all", "we", "our", "if", "not", "no", "there",
    "current", "about", "how", "why", "when", "into", "than", "then", "but",
    "its", "has", "have", "been", "was", "were", "will", "would", "could",
    "should", "may", "might", "must", "shall", "being", "more", "most", "some",
    "such", "only", "other", "over", "under", "between", "within", "without",
}

# The exact stopword list of the MVP round, kept verbatim so the frozen
# baseline_mvp mode can be reproduced byte-for-byte. Widening STOPWORDS is a
# real improvement ("than", "between" carry no topical information and were
# inflating score denominators), but a reference configuration that drifts when
# the tokenizer improves is not a reference. Do not edit this set.
MVP_STOPWORDS = {
    "the", "a", "an", "of", "to", "in", "is", "are", "can", "does", "do", "for",
    "and", "or", "on", "by", "with", "what", "which", "that", "this", "it", "as",
    "be", "from", "at", "any", "all", "we", "our", "if", "not", "no", "there",
    "current", "about", "how", "why", "when",
}

# Words that are mathematically ubiquitous and topically empty. Excluded from
# relevance scoring for EVERY query. This is the fix that does not depend on
# anybody having listed the external subject in advance.
GENERIC_TERMS = {
    "hypothesis", "hypotheses", "conjecture", "conjectures", "theorem", "theorems",
    "lemma", "proof", "proofs", "result", "results", "problem", "problems",
    "question", "questions", "mathematics", "math", "imply", "implies",
    "implication", "anything", "something", "here", "repository", "repo",
    "paper", "literature", "work", "approach", "method", "technique", "techniques",
    "idea", "ideas", "help", "helps", "useful", "relevant", "related", "say",
}

# The reader is asking to import an idea, not claiming the repository studies
# the external subject. These queries must pass through.
#
# Matched on WORD BOUNDARIES, not as bare substrings. Substring matching was a
# bug: "port" matches "transport" (and EOC has a TransportCollapse module),
# "apply" matches "misapply". Bare "apply"/"applied" are also dropped, because
# "how do the Navier-Stokes results apply?" asserts that those results are here
# rather than asking whether they could be carried over. Phrases that clearly
# signal import are kept.
TRANSFER_INTENT = (
    "analog", "analogy", "analogous", "transfer", "transfers", "borrow",
    "adapt", "adapted", "adaptable", "carry over", "carries over",
    "inspire", "inspired", "lesson", "lessons", "similar", "similarity",
    "compare", "comparison", "parallel", "applicable",
    "technique from", "techniques from", "ideas from", "idea from",
    "methods from", "method from", "results from", "literature",
    "help with", "help the", "bearing on", "cross-pollinat",
)


def detect_external(query: str) -> list[str]:
    return [label for label, _ in _detect_external_with_spans(query)]


def _detect_external_with_spans(query: str) -> list[tuple[str, set[str]]]:
    """Matched external subjects, each with the query words its phrase consumed."""
    q = query.lower()
    found = []
    for label, phrases in EXTERNAL_SUBJECTS.items():
        consumed: set[str] = set()
        hit = False
        for ph in phrases:
            if ph in q:
                hit = True
                consumed |= set(re.findall(r"[a-z][a-z0-9_]*", ph))
        if hit:
            found.append((label, consumed))
    return found


def detect_transfer_intent(query: str) -> list[str]:
    q = query.lower()
    return [t for t in TRANSFER_INTENT
            if re.search(r"(?<![a-z])" + re.escape(t) + r"(?![a-z])", q)]


# How many distinct repository terms a query must contain before an externally
# grounded question is treated as a transfer request rather than refused.
SUBSTANTIAL_TOPICAL = 2


def classify(query: str, repo_vocab: set[str]) -> dict:
    """Classify a query before retrieval runs.

    verdict is one of:
      IN_DOMAIN          -- proceed normally
      TRANSFER_REQUEST   -- external subject named, but transfer explicitly asked
                            for; proceed, labelled
      OUT_OF_DOMAIN      -- external subject named with no repository footing;
                            refuse to rank Collatz material as an answer
      WEAK_MATCH         -- no external subject, but nothing topical matched
                            either; proceed with a warning
    """
    spans = _detect_external_with_spans(query)
    external = [label for label, _ in spans]
    consumed: set[str] = set()
    for _, words in spans:
        consumed |= words
    transfer = detect_transfer_intent(query)
    toks = {w for w in re.findall(r"[a-z][a-z0-9_]*", query.lower())}
    # Words belonging to the matched external phrase cannot also serve as
    # evidence that the question is grounded in this repository. Without this,
    # "Is the Yang-Mills MASS GAP addressed?" cleared the two-term threshold
    # because EOC happens to use "mass" and has a LiftGap module, and the
    # question then returned unrelated deficit nodes. The external term's own
    # vocabulary is not repository grounding.
    topical = (toks - GENERIC_TERMS - STOPWORDS - consumed) & repo_vocab

    if external and transfer:
        verdict = "TRANSFER_REQUEST"
    elif external and not topical:
        verdict = "OUT_OF_DOMAIN"
    elif external and len(topical) >= SUBSTANTIAL_TOPICAL:
        # Names an external subject AND enough repository vocabulary to be
        # worth answering: passed through, labelled, rather than refused.
        # The threshold is not cosmetic. With a threshold of one, "Is the
        # Yang-Mills mass GAP addressed?" passed because EOC has a LiftGap
        # module, and "Does Goldbach FACTOR into the argument?" passed on
        # "factor" -- both then returned unrelated deficit and Curry nodes.
        # One incidental word is coincidence; two is a topic.
        verdict = "TRANSFER_REQUEST"
    elif external:
        verdict = "OUT_OF_DOMAIN"
    elif not topical:
        verdict = "WEAK_MATCH"
    else:
        verdict = "IN_DOMAIN"

    return {
        "verdict": verdict,
        "external_subjects": external,
        "transfer_intent": transfer,
        "topical_terms": sorted(topical),
        "external_phrase_words_discounted": sorted(consumed & repo_vocab),
        "generic_terms_ignored": sorted(toks & GENERIC_TERMS),
    }


def repo_vocabulary(sem: dict, graph: dict) -> set[str]:
    """Domain vocabulary, derived from the repository rather than hand-written.

    Built from semantic-node keywords, titles and ids, module basenames and
    declaration name fragments. Generic terms are removed, so the vocabulary
    cannot re-admit the very words the guard exists to discount.
    """
    vocab: set[str] = set()

    def add(text: str) -> None:
        vocab.update(re.findall(r"[a-z][a-z0-9]*", text.lower()))

    for n in sem["nodes"]:
        add(n.get("id", ""))
        add(n.get("title", ""))
        for k in n.get("keywords", []):
            add(k)
    for d in graph["declarations"].values():
        if not d.get("generated"):
            add(d["module"].replace(".", " "))
            add(d["name"].split(".")[-1].replace("_", " "))
    # split CamelCase module words too (BlockCube -> block, cube)
    extra: set[str] = set()
    for d in graph["declarations"].values():
        for part in d["module"].split("."):
            for w in re.findall(r"[A-Z][a-z]+|[a-z]+", part):
                extra.add(w.lower())
    vocab |= extra
    vocab -= GENERIC_TERMS
    vocab -= STOPWORDS
    return {v for v in vocab if len(v) > 2}


OOD_MESSAGE = """\
## NO DIRECT REPOSITORY EVIDENCE

This question names mathematics this repository has not studied: {subjects}.

Nothing in the formal library or the research documents addresses it, so no
ranked list of Collatz material is offered — any such list would be a false
positive produced by shared vocabulary, not by relevance.

The repository *can* still be searched for an analogy if that is what you want.
Ask explicitly, for example:

> Could a technique from the {first} literature help the EOC arithmetic bottleneck?

and the query will be treated as a transfer request rather than refused.
"""
