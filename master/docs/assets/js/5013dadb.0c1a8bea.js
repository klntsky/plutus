"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[2227],{7566:(e,n,t)=>{t.r(n),t.d(n,{assets:()=>s,contentTitle:()=>u,default:()=>l,frontMatter:()=>o,metadata:()=>a,toc:()=>d});var i=t(4848),r=t(8453);const o={sidebar_position:20},u="ADR 3: Sharing code between the production and debugging CEK machine",a={id:"adr/adr3",title:"ADR 3: Sharing code between the production and debugging CEK machine",description:"Date: 2022-10",source:"@site/docs/adr/adr3.md",sourceDirName:"adr",slug:"/adr/adr3",permalink:"/plutus/master/docs/adr/adr3",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/adr/adr3.md",tags:[],version:"current",sidebarPosition:20,frontMatter:{sidebar_position:20},sidebar:"tutorialSidebar",previous:{title:"ADR 2: Steppable CEK machine",permalink:"/plutus/master/docs/adr/adr2"},next:{title:"ADR 4: Deferred unlifting in Plutus Core",permalink:"/plutus/master/docs/adr/adr4"}},s={},d=[{value:"Authors",id:"authors",level:2},{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"Decision: Polymorphic compute/return steps",id:"decision-polymorphic-computereturn-steps",level:2},{value:"Detailed description with code snippets",id:"detailed-description-with-code-snippets",level:3},{value:"Implications",id:"implications",level:2}];function c(e){const n={a:"a",code:"code",h1:"h1",h2:"h2",h3:"h3",li:"li",p:"p",pre:"pre",ul:"ul",...(0,r.R)(),...e.components};return(0,i.jsxs)(i.Fragment,{children:[(0,i.jsx)(n.h1,{id:"adr-3-sharing-code-between-the-production-and-debugging-cek-machine",children:"ADR 3: Sharing code between the production and debugging CEK machine"}),"\n",(0,i.jsx)(n.p,{children:"Date: 2022-10"}),"\n",(0,i.jsx)(n.h2,{id:"authors",children:"Authors"}),"\n",(0,i.jsx)(n.p,{children:(0,i.jsx)(n.a,{href:"mailto:marty.stumpf@iohk.io",children:"Marty Stumpf"})}),"\n",(0,i.jsx)(n.h2,{id:"status",children:"Status"}),"\n",(0,i.jsx)(n.p,{children:"Draft"}),"\n",(0,i.jsx)(n.h2,{id:"context",children:"Context"}),"\n",(0,i.jsx)(n.p,{children:"In order to have a minimal viable product of a debugger for Plutus, we need a CEK machine that will give us more information for debugging than our current one."}),"\n",(0,i.jsx)(n.p,{children:"One of the first decision we need to make is: should the debugging machine be a separate one?\nThe debugging machine needs to satisfy these requirements:"}),"\n",(0,i.jsxs)(n.ul,{children:["\n",(0,i.jsx)(n.li,{children:"We must not compromise the performance of the production machine, and"}),"\n",(0,i.jsx)(n.li,{children:"The debugging machine must behave the same as the production machine."}),"\n"]}),"\n",(0,i.jsx)(n.p,{children:"There are tradeoffs between these two requirements.\nIf we have a separate machine, the performance of the production machine will be untouched.\nBut there is more scope for us to make mistakes with the new machine."}),"\n",(0,i.jsx)(n.p,{children:"However, if we share code between the two machines, the performance of the production machine may be compromised."}),"\n",(0,i.jsx)(n.p,{children:"This ADR proposes an approach for the two machines to share code while not compromising performance."}),"\n",(0,i.jsx)(n.h2,{id:"decision-polymorphic-computereturn-steps",children:"Decision: Polymorphic compute/return steps"}),"\n",(0,i.jsxs)(n.p,{children:["As long as the debugging machine has the same type, we can alter ",(0,i.jsx)(n.code,{children:"computeCek"}),"/",(0,i.jsx)(n.code,{children:"returnCek"})," to be polymorphic over a type-level ",(0,i.jsx)(n.code,{children:"Bool"})," specifying if we\u2019re in debug mode or not.\nThen we demote it to the term level in the definition of ",(0,i.jsx)(n.code,{children:"computeCek"}),"/",(0,i.jsx)(n.code,{children:"returnCek"})," and branch on the ",(0,i.jsx)(n.code,{children:"Bool"})," thus implementing different logic depending on whether we're in debug mode or not.\nThis promotion to the type level allows us to statically instantiate the ",(0,i.jsx)(n.code,{children:"Bool"})," in an instance and thus make GHC compile the whole worker of the CEK machine twice: once in debug mode and once in production mode.\nTheoretically, GHC will take care to remove all the dead debug code when in production mode."]}),"\n",(0,i.jsx)(n.h3,{id:"detailed-description-with-code-snippets",children:"Detailed description with code snippets"}),"\n",(0,i.jsxs)(n.p,{children:["Whether we are debugging or not, we will be returning a ",(0,i.jsx)(n.code,{children:"CekState"}),":"]}),"\n",(0,i.jsx)(n.pre,{children:(0,i.jsx)(n.code,{className:"language-haskell",children:"data CekState uni fun =\n    -- the next state is computing\n    Computing WordArray (Context uni fun) (Closure uni fun)\n    -- the next state is returning\n    | Returning WordArray (Context uni fun) (CekValue uni fun)\n    -- evaluation finished\n    | Terminating (Term NamedDeBruijn uni fun ())\n\ndata Closure uni fun = \n  Closure (Term NamedDeBruijn uni fun ()) (CekValEnv uni fun)\n"})}),"\n",(0,i.jsxs)(n.p,{children:["We enter either modes via ",(0,i.jsx)(n.code,{children:"enterComputeCek"}),", which takes an extra ",(0,i.jsx)(n.code,{children:"Bool"})," than our current implementation, to indicate whether we are in debugging mode or not:"]}),"\n",(0,i.jsx)(n.pre,{children:(0,i.jsx)(n.code,{className:"language-haskell",children:"enterComputeCek \n    :: forall uni fun s\n    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)\n    => Bool\n    -> Context uni fun\n    -> Closure uni fun\n    -> CekM uni fun s (CekState uni fun)\nenterComputeCek debug ctx (Closure term env) =\n    -- The initial step is always computing with zero budget, empty context and environment.\n    -- `computeCekStep` matches on the `term` and calls `computeCek` or `returnCek` depending on the clause. \n    computeCekStep (toWordArray 0) NoFrame (Closure term Env.empty) where\n    \n    computeCek\n        :: WordArray -- for costing\n        -> Context uni fun\n        -> Closure uni fun\n        -> CekM uni fun s (CekState uni fun)\n    computeCek = if debug then computeCekDebug else computeCekStep\n    {-# NOINLINE computeCek #-}  -- Making sure the `if` is only evaluated once.\n\n    -- in debugging mode, immediately returns the current `CekState` and halts execution. Debugging mode details to be worked out.\n    computeCekDebug \n        :: WordArray\n        -> Context uni fun\n        -> Closure uni fun\n        -> CekM uni fun s (CekState uni fun) \n    computeCekDebug budget ctx (Closure term env) = \n        pure $ Computing budget ctx (Closure term env)\n\n    -- In production mode, `computeCekStep` matches on the term and calls `computeCek` or `returnCek` on a subterm. \n    -- In production mode, `computeCek` calls the original `computeCekStep`, i.e. in production mode `computeCekStep` calls itself through the thin `computeCek` wrapper thus achieving recursion and replicating the old behavior of the CEK machine.\n    computeCekStep \n        :: WordArray\n        -> Context uni fun\n        -> Closure uni fun\n        -> CekM uni fun s (CekState uni fun) -- the return type is `CekState` instead of a term.\n    computeCekStep unbudgetedSteps ctx (Closure (Force _ body) env) = do -- exactly like in current prod\n        !unbudgetedSteps' <- stepAndMaybeSpend BForce unbudgetedSteps -- update costs\n        computeCek unbudgetedSteps' (FrameForce ctx) (Closure body env) -- compute again with updated costs and ctx\n    <other_clauses> -- there's a lot of code in here! Some clauses call `returnCek`, some `computeCek`, achieving recursive calling similar to our current implementation. \n    \n    -- details of `forceEvaluate`, `applyEvaluate` etc to be worked out.\n\n    -- similarly for the returning step\n\n    returnCek = if debug then returnCekDebug else returnCekStep\n    {-# NOINLINE returnCek #-}\n    \n    returnCekDebug = ...\n\n    \n    returnCekStep \n        :: forall uni fun s\n        . (PrettyUni uni fun, GivenCekReqs uni fun s)\n        => WordArray\n        -> Context uni fun\n        -> CekValue uni fun\n        -> CekM uni fun s (CekState uni fun) -- return a state instead of a term\n    returnCekStep !unbudgetedSteps NoFrame val = do\n    spendAccumulatedBudget unbudgetedSteps\n    pure $ Terminating $ dischargeCekValue val --wrap the term in the `Terminating` constructor when returning the term.\n    <other_clauses>\n"})}),"\n",(0,i.jsxs)(n.p,{children:['This trick lets us inline the "step" functions and call them recursively like before.\nBecause when we are not debugging, we are still using basically the same code as our current implementation, the performance should not be affected by much.\n(Given that the machine is tail-recursive, the additional wrapping of the returned term in the ',(0,i.jsx)(n.code,{children:"Terminating"})," constructor will affect performance in a negligible way.)"]}),"\n",(0,i.jsx)(n.h2,{id:"implications",children:"Implications"}),"\n",(0,i.jsx)(n.p,{children:"This is a draft of an idea.\nThere are further details to be worked out in a prototype.\nThe implementor should use their own judgement."}),"\n",(0,i.jsx)(n.p,{children:"Whether we proceed with this approach or not depends on how the prototyping goes, and its benchmarking results.\nIf we find that the slow down is negligible enough, then we may proceed with this.\nOtherwise, we proceed with a separate implementation for the debugging machine."})]})}function l(e={}){const{wrapper:n}={...(0,r.R)(),...e.components};return n?(0,i.jsx)(n,{...e,children:(0,i.jsx)(c,{...e})}):c(e)}},8453:(e,n,t)=>{t.d(n,{R:()=>u,x:()=>a});var i=t(6540);const r={},o=i.createContext(r);function u(e){const n=i.useContext(o);return i.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function a(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:u(e.components),i.createElement(o.Provider,{value:n},e.children)}}}]);