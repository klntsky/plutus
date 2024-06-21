"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[7987],{7553:(e,t,s)=>{s.r(t),s.d(t,{assets:()=>o,contentTitle:()=>a,default:()=>c,frontMatter:()=>l,metadata:()=>r,toc:()=>d});var n=s(4848),i=s(8453);const l={sidebar_position:15},a="Writing Plutus Tx programs",r={id:"using-plutus-tx/writing-plutus-tx-programs",title:"Writing Plutus Tx programs",description:"Template Haskell preliminaries",source:"@site/docs/using-plutus-tx/writing-plutus-tx-programs.md",sourceDirName:"using-plutus-tx",slug:"/using-plutus-tx/writing-plutus-tx-programs",permalink:"/plutus/master/docs/using-plutus-tx/writing-plutus-tx-programs",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/using-plutus-tx/writing-plutus-tx-programs.md",tags:[],version:"current",sidebarPosition:15,frontMatter:{sidebar_position:15},sidebar:"tutorialSidebar",previous:{title:"High-level overview of how Plutus Tx works",permalink:"/plutus/master/docs/using-plutus-tx/overview-plutus-tx"},next:{title:"Compiling Plutus Tx",permalink:"/plutus/master/docs/using-plutus-tx/compiling-plutus-tx"}},o={},d=[{value:"Template Haskell preliminaries",id:"template-haskell-preliminaries",level:2},{value:"Simple pattern",id:"simple-pattern",level:2},{value:"Quotes",id:"quotes",level:2},{value:"Splicing quotes",id:"splicing-quotes",level:2},{value:"Necessary language extensions for the Plutus Tx compiler to work",id:"necessary-language-extensions-for-the-plutus-tx-compiler-to-work",level:2},{value:"Plutus Tx standard usage pattern (how all of our Plutus Tx programs are written)",id:"plutus-tx-standard-usage-pattern-how-all-of-our-plutus-tx-programs-are-written",level:2},{value:"Functions and datatypes",id:"functions-and-datatypes",level:2},{value:"Normal Haskell datatypes and pattern matching",id:"normal-haskell-datatypes-and-pattern-matching",level:2},{value:"Example",id:"example",level:3},{value:"Typeclasses",id:"typeclasses",level:2},{value:"The Plutus Tx Prelude",id:"the-plutus-tx-prelude",level:2},{value:"Plutus Tx Prelude has redefined versions of many standard typeclasses",id:"plutus-tx-prelude-has-redefined-versions-of-many-standard-typeclasses",level:3},{value:"Lifting values for generating code dynamically",id:"lifting-values-for-generating-code-dynamically",level:2}];function u(e){const t={blockquote:"blockquote",code:"code",em:"em",h1:"h1",h2:"h2",h3:"h3",li:"li",p:"p",strong:"strong",ul:"ul",...(0,i.R)(),...e.components},{LiteralInclude:s}=t;return s||function(e,t){throw new Error("Expected "+(t?"component":"object")+" `"+e+"` to be defined: you likely forgot to import, pass, or provide it.")}("LiteralInclude",!0),(0,n.jsxs)(n.Fragment,{children:[(0,n.jsx)(t.h1,{id:"writing-plutus-tx-programs",children:"Writing Plutus Tx programs"}),"\n",(0,n.jsx)(t.h2,{id:"template-haskell-preliminaries",children:"Template Haskell preliminaries"}),"\n",(0,n.jsx)(t.p,{children:"Plutus Tx uses Haskell's metaprogramming support, Template Haskell, for two main reasons:"}),"\n",(0,n.jsxs)(t.ul,{children:["\n",(0,n.jsx)(t.li,{children:"Template Haskell enables us to work at compile time, which is when we do Plutus Tx compilation."}),"\n",(0,n.jsx)(t.li,{children:"It allows us to wire up the machinery that invokes the Plutus Tx compiler."}),"\n"]}),"\n",(0,n.jsx)(t.h2,{id:"simple-pattern",children:"Simple pattern"}),"\n",(0,n.jsx)(t.p,{children:"Template Haskell is very versatile, but we only use a few features.\nEssentially, we often use the same simple pattern:"}),"\n",(0,n.jsxs)(t.ul,{children:["\n",(0,n.jsx)(t.li,{children:"make a quote,"}),"\n",(0,n.jsxs)(t.li,{children:["immediately call ",(0,n.jsx)(t.code,{children:"PlutusTx.TH.compile"}),", and then"]}),"\n",(0,n.jsx)(t.li,{children:"splice the result back in."}),"\n"]}),"\n",(0,n.jsx)(t.h2,{id:"quotes",children:"Quotes"}),"\n",(0,n.jsxs)(t.p,{children:["Template Haskell begins with ",(0,n.jsx)(t.em,{children:"quotes"}),". A Template Haskell quote is a Haskell expression ",(0,n.jsx)(t.code,{children:"e"})," inside special brackets ",(0,n.jsx)(t.code,{children:"[|| e ||]"}),".\nIt has type ",(0,n.jsx)(t.code,{children:"Q (TExp a)"})," where ",(0,n.jsx)(t.code,{children:"e"})," has type ",(0,n.jsx)(t.code,{children:"a"}),".\n",(0,n.jsx)(t.code,{children:"TExp a"})," is a ",(0,n.jsx)(t.em,{children:"representation"})," of an expression of type ",(0,n.jsx)(t.code,{children:"a"}),"; in other words, the syntax of the actual Haskell expression that was quoted.\nThe quote lives in the type ",(0,n.jsx)(t.code,{children:"Q"})," of quotes, which isn't very interesting for us."]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsxs)(t.p,{children:["There is also an abbreviation ",(0,n.jsx)(t.code,{children:"TExpQ a"})," for ",(0,n.jsx)(t.code,{children:"Q (TExp a)"}),", which avoids some parentheses."]}),"\n"]}),"\n",(0,n.jsx)(t.h2,{id:"splicing-quotes",children:"Splicing quotes"}),"\n",(0,n.jsxs)(t.p,{children:["You can ",(0,n.jsx)(t.em,{children:"splice"})," a quote into your program using the ",(0,n.jsx)(t.code,{children:"$$"})," operator.\nThis inserts the syntax represented by the quote into the program at the point where the splice is written."]}),"\n",(0,n.jsxs)(t.p,{children:["Simply put, a quote allows us to talk about Haskell programs as ",(0,n.jsx)(t.em,{children:"values"}),"."]}),"\n",(0,n.jsxs)(t.p,{children:["The Plutus Tx compiler compiles Haskell ",(0,n.jsx)(t.em,{children:"expressions"})," (not values), so naturally it takes a quote (representing an expression) as an argument.\nThe result is a new quote, this time for a Haskell program that represents the ",(0,n.jsx)(t.em,{children:"compiled"})," program.\nIn Haskell, the type of ",(0,n.jsx)(t.code,{children:"PlutusTx.TH.compile"})," is ",(0,n.jsx)(t.code,{children:"TExpQ a \u2192 TExpQ (CompiledCode a)"}),".\nThis is just what we already said:"]}),"\n",(0,n.jsxs)(t.ul,{children:["\n",(0,n.jsxs)(t.li,{children:[(0,n.jsx)(t.code,{children:"TExpQ a"})," is a quote representing a program of type ",(0,n.jsx)(t.code,{children:"a"}),"."]}),"\n",(0,n.jsxs)(t.li,{children:[(0,n.jsx)(t.code,{children:"TExpQ (CompiledCode a)"})," is a quote representing a compiled Plutus Core program."]}),"\n"]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsxs)(t.p,{children:[(0,n.jsx)(t.code,{children:"PlutusTx.CompiledCode"})," also has a type parameter ",(0,n.jsx)(t.code,{children:"a"}),", which corresponds to the type of the original expression."]}),"\n",(0,n.jsx)(t.p,{children:'This lets us "remember" the type of the original Haskell program we compiled.'}),"\n"]}),"\n",(0,n.jsxs)(t.p,{children:["Since ",(0,n.jsx)(t.code,{children:"PlutusTx.TH.compile"})," produces a quote, to use the result we need to splice it back into our program.\nThe Plutus Tx compiler runs when compiling the main program, and the compiled program will be inserted into the main program."]}),"\n",(0,n.jsx)(t.h2,{id:"necessary-language-extensions-for-the-plutus-tx-compiler-to-work",children:"Necessary language extensions for the Plutus Tx compiler to work"}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Language extensions",start:"-- BLOCK1",end:"-- BLOCK2"}),"\n",(0,n.jsxs)(t.p,{children:["This simple program just evaluates to the integer ",(0,n.jsx)(t.code,{children:"1"}),"."]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsx)(t.p,{children:"The examples that show the Plutus Core generated from compilation include doctests.\nThe syntax of Plutus Core might look unfamiliar, since this syntax is used for the 'assembly language,' which means you don't need to inspect the compiler's output."}),"\n"]}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"integerOne simple program",start:"-- BLOCK2",end:"-- BLOCK3"}),"\n",(0,n.jsxs)(t.p,{children:["We can see how the metaprogramming works: the Haskell program ",(0,n.jsx)(t.code,{children:"1"})," was turned into a ",(0,n.jsx)(t.code,{children:"CompiledCode Integer"})," at compile time, which we spliced into our Haskell program.\nWe can inspect the generated program at runtime to see the generated Plutus Core (or to put it on the blockchain)."]}),"\n",(0,n.jsx)(t.h2,{id:"plutus-tx-standard-usage-pattern-how-all-of-our-plutus-tx-programs-are-written",children:"Plutus Tx standard usage pattern (how all of our Plutus Tx programs are written)"}),"\n",(0,n.jsxs)(t.p,{children:["We also see the standard usage pattern: a TH quote, wrapped in a call to ",(0,n.jsx)(t.code,{children:"PlutusTx.TH.compile"}),", wrapped in a ",(0,n.jsx)(t.code,{children:"$$"})," splice.\nThis is how all our Plutus Tx programs are written."]}),"\n",(0,n.jsx)(t.p,{children:"The following is a slightly more complex program.\nIt includes the identity function on integers."}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Identity function on integers",start:"-- BLOCK3",end:"-- BLOCK4"}),"\n",(0,n.jsx)(t.h2,{id:"functions-and-datatypes",children:"Functions and datatypes"}),"\n",(0,n.jsx)(t.p,{children:"You can use functions inside your expression.\nIn practice, you will usually want to define the entirety of your Plutus Tx program as a definition outside the quote, and then simply call it inside the quote."}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Functions and datatypes",start:"-- BLOCK4",end:"-- BLOCK5"}),"\n",(0,n.jsx)(t.h2,{id:"normal-haskell-datatypes-and-pattern-matching",children:"Normal Haskell datatypes and pattern matching"}),"\n",(0,n.jsx)(t.p,{children:"We can use normal Haskell datatypes and pattern matching freely:"}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Normal Haskell datatypes and pattern matching",start:"-- BLOCK5",end:"-- BLOCK6"}),"\n",(0,n.jsxs)(t.p,{children:["Unlike functions, datatypes do not need any kind of special annotation to be used inside a quote, hence we can use types like ",(0,n.jsx)(t.code,{children:"Maybe"})," from the Haskell ",(0,n.jsx)(t.code,{children:"Prelude"}),".\nThis works for your own datatypes too."]}),"\n",(0,n.jsx)(t.h3,{id:"example",children:"Example"}),"\n",(0,n.jsx)(t.p,{children:"Here's a small example with a datatype representing a potentially open-ended end date."}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Datatype representing a potentially open-ended end date",start:"-- BLOCK6",end:"-- BLOCK7"}),"\n",(0,n.jsxs)(t.p,{children:["We could also have defined the ",(0,n.jsx)(t.code,{children:"pastEnd"})," function as a separate ",(0,n.jsx)(t.code,{children:"INLINABLE"})," binding and just referred to it in the quote, but in this case, it's small enough to just write in place."]}),"\n",(0,n.jsx)(t.h2,{id:"typeclasses",children:"Typeclasses"}),"\n",(0,n.jsxs)(t.p,{children:["So far we have used functions like ",(0,n.jsx)(t.code,{children:"lessThanEqInteger"})," for comparing ",(0,n.jsx)(t.code,{children:"Integer"}),"s, which is much less convenient than ",(0,n.jsx)(t.code,{children:"<"})," from the standard Haskell ",(0,n.jsx)(t.code,{children:"Ord"})," typeclass."]}),"\n",(0,n.jsxs)(t.p,{children:["While Plutus Tx does support typeclasses, we cannot use many of the standard typeclasses, since we require their class methods to be ",(0,n.jsx)(t.code,{children:"INLINABLE"}),", and the implementations for types such as ",(0,n.jsx)(t.code,{children:"Integer"})," use the Plutus Tx built-ins."]}),"\n",(0,n.jsx)(t.h2,{id:"the-plutus-tx-prelude",children:"The Plutus Tx Prelude"}),"\n",(0,n.jsxs)(t.p,{children:["The ",(0,n.jsx)(t.code,{children:"PlutusTx.Prelude"})," module is a drop-in replacement for the normal Haskell Prelude, with some redefined functions and typeclasses that make it easier for the Plutus Tx compiler to handle (such as ",(0,n.jsx)(t.code,{children:"INLINABLE"}),")."]}),"\n",(0,n.jsx)(t.p,{children:"Use the Plutus Tx Prelude for code that you expect to compile with the Plutus Tx compiler.\nAll the definitions in the Plutus Tx Prelude include working Haskell definitions, which means that you can use them in normal Haskell code too, although for normal Haskell code, the Haskell Prelude versions will probably perform better."}),"\n",(0,n.jsxs)(t.p,{children:["To use the Plutus Tx Prelude, use the ",(0,n.jsx)(t.code,{children:"NoImplicitPrelude"})," language pragma and import ",(0,n.jsx)(t.code,{children:"PlutusTx.Prelude"}),"."]}),"\n",(0,n.jsx)(t.p,{children:"Plutus Tx includes some built-in types and functions for working with primitive data (integers and bytestrings), as well as a few special functions.\nThese types are also exported from the Plutus Tx Prelude."}),"\n",(0,n.jsx)(t.h3,{id:"plutus-tx-prelude-has-redefined-versions-of-many-standard-typeclasses",children:"Plutus Tx Prelude has redefined versions of many standard typeclasses"}),"\n",(0,n.jsx)(t.p,{children:"Redefined versions of many standard typeclasses are available in the Plutus Tx Prelude.\nAs such, you should be able to use most typeclass functions in your Plutus Tx programs."}),"\n",(0,n.jsxs)(t.p,{children:["For example, the following is a version of the ",(0,n.jsx)(t.code,{children:"pastEnd"})," function using ",(0,n.jsx)(t.code,{children:"<"}),".\nThis will be compiled to exactly the same code as the previous definition."]}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"A version of the `pastEnd` function",start:"-- BLOCK7",end:"-- BLOCK8"}),"\n",(0,n.jsx)(t.h2,{id:"lifting-values-for-generating-code-dynamically",children:"Lifting values for generating code dynamically"}),"\n",(0,n.jsxs)(t.p,{children:["So far, we've seen how to define pieces of code ",(0,n.jsx)(t.em,{children:"statically"})," (when you ",(0,n.jsx)(t.em,{children:"compile"})," your main Haskell program), but you might want to generate code ",(0,n.jsx)(t.em,{children:"dynamically"})," (that is, when you ",(0,n.jsx)(t.em,{children:"run"})," your main Haskell program).\nFor example, you might be writing the body of a transaction to initiate a crowdfunding smart contract, which would need to be parameterized by data determining the size of the goal, the campaign start and end times, and any additional data that may be required."]}),"\n",(0,n.jsxs)(t.p,{children:["We can do this in the same way that we parameterize code in functional programming: writing the static code as a ",(0,n.jsx)(t.em,{children:"function"})," and providing the argument later to configure it."]}),"\n",(0,n.jsxs)(t.p,{children:["In our case, there is a slight complication: we want to make the argument and apply the function to it at ",(0,n.jsx)(t.em,{children:"runtime"}),".\nPlutus Tx addresses this through ",(0,n.jsx)(t.em,{children:"lifting"}),".\nLifting enables the use of the same types, both inside your Plutus Tx program ",(0,n.jsx)(t.em,{children:"and"})," in the external code that uses it."]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsxs)(t.p,{children:["In this context, ",(0,n.jsx)(t.em,{children:"runtime"})," means the runtime of the main Haskell program, ",(0,n.jsx)(t.strong,{children:"not"})," when the Plutus Core runs on the chain.\nWe want to configure our code when the main Haskell program runs, as that is when we will be getting user input."]}),"\n"]}),"\n",(0,n.jsx)(t.p,{children:"In this example, we add an add-one function."}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Example of lifting",start:"-- BLOCK8",end:"-- BLOCK9"}),"\n",(0,n.jsxs)(t.p,{children:["Now, suppose we want to apply this to ",(0,n.jsx)(t.code,{children:"4"})," at runtime, giving us a program that computes to ",(0,n.jsx)(t.code,{children:"5"}),".\nWe need to ",(0,n.jsx)(t.em,{children:"lift"})," the argument (",(0,n.jsx)(t.code,{children:"4"}),") from Haskell to Plutus Core, and then we need to apply the function to it."]}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"Lift the argument (`4`) from Haskell to Plutus Core",start:"-- BLOCK9",end:"-- BLOCK10"}),"\n",(0,n.jsxs)(t.p,{children:["We lifted the argument using the ",(0,n.jsx)(t.code,{children:"PlutusTx.liftCode"})," function.\nTo use this, a type must have an instance of the ",(0,n.jsx)(t.code,{children:"PlutusTx.Lift"})," class.\nFor your own datatypes, you should generate these with the ",(0,n.jsx)(t.code,{children:"PlutusTx.makeLift"})," TH function from ",(0,n.jsx)(t.code,{children:"PlutusTx.Lift"}),"."]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsxs)(t.p,{children:[(0,n.jsx)(t.code,{children:"PlutusTx.liftCode"})," is relatively unsafe because it ignores any errors that might occur from lifting something that might not be supported.\nThere is a ",(0,n.jsx)(t.code,{children:"PlutusTx.safeLiftCode"})," if you want to explicitly handle these occurrences."]}),"\n"]}),"\n",(0,n.jsx)(t.p,{children:"The combined program applies the original compiled lambda to the lifted value (notice that the lambda is a bit complicated now, since we have compiled the addition into a built-in)."}),"\n",(0,n.jsxs)(t.p,{children:["Here's an example with our custom datatype. The output is the encoded version of ",(0,n.jsx)(t.code,{children:"False"}),"."]}),"\n",(0,n.jsx)(s,{file:"BasicPlutusTx.hs",language:"haskell",title:"An example with our custom datatype",start:"-- BLOCK10",end:"-- BLOCK11"})]})}function c(e={}){const{wrapper:t}={...(0,i.R)(),...e.components};return t?(0,n.jsx)(t,{...e,children:(0,n.jsx)(u,{...e})}):u(e)}},8453:(e,t,s)=>{s.d(t,{R:()=>a,x:()=>r});var n=s(6540);const i={},l=n.createContext(i);function a(e){const t=n.useContext(l);return n.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function r(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(i):e.components||i:a(e.components),n.createElement(l.Provider,{value:t},e.children)}}}]);