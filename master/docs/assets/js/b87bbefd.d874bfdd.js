"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[8875],{4507:(e,t,s)=>{s.r(t),s.d(t,{assets:()=>l,contentTitle:()=>a,default:()=>p,frontMatter:()=>n,metadata:()=>o,toc:()=>u});var i=s(4848),r=s(8453);const n={sidebar_position:30},a="Libraries for writing Plutus Tx scripts",o={id:"simple-example/libraries",title:"Libraries for writing Plutus Tx scripts",description:"This auction example shows a relatively low-level way of writing scripts using Plutus Tx.",source:"@site/docs/simple-example/libraries.md",sourceDirName:"simple-example",slug:"/simple-example/libraries",permalink:"/plutus/master/docs/simple-example/libraries",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/simple-example/libraries.md",tags:[],version:"current",sidebarPosition:30,frontMatter:{sidebar_position:30},sidebar:"tutorialSidebar",previous:{title:"Life cycle of the auction smart contract",permalink:"/plutus/master/docs/simple-example/life-cycle"},next:{title:"Alternatives to Plutus Tx",permalink:"/plutus/master/docs/simple-example/alternatives-to-plutus-tx"}},l={},u=[];function c(e){const t={a:"a",code:"code",h1:"h1",p:"p",...(0,r.R)(),...e.components};return(0,i.jsxs)(i.Fragment,{children:[(0,i.jsx)(t.h1,{id:"libraries-for-writing-plutus-tx-scripts",children:"Libraries for writing Plutus Tx scripts"}),"\n",(0,i.jsxs)(t.p,{children:["This auction example shows a relatively low-level way of writing scripts using Plutus Tx.\nIn practice, you may consider using a higher-level library that abstracts away some of the details.\nFor example, ",(0,i.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus-apps",children:"plutus-apps"})," provides a constraint library for writing Plutus Tx.\nUsing these libraries, writing a validator in Plutus Tx becomes a matter of defining state transactions and the corresponding constraints, e.g., the condition ",(0,i.jsx)(t.code,{children:"refundsPreviousHighestBid"})," can simply be written as ",(0,i.jsx)(t.code,{children:"Constraints.mustPayToPubKey bidder (lovelaceValue amt)"}),"."]})]})}function p(e={}){const{wrapper:t}={...(0,r.R)(),...e.components};return t?(0,i.jsx)(t,{...e,children:(0,i.jsx)(c,{...e})}):c(e)}},8453:(e,t,s)=>{s.d(t,{R:()=>a,x:()=>o});var i=s(6540);const r={},n=i.createContext(r);function a(e){const t=i.useContext(n);return i.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function o(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:a(e.components),i.createElement(n.Provider,{value:t},e.children)}}}]);