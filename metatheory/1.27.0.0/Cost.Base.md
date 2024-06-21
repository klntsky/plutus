
<pre class="Agda"><a id="6" class="Keyword">module</a> <a id="13" href="Cost.Base.html" class="Module">Cost.Base</a> <a id="23" class="Keyword">where</a> 

</pre>
## Imports

<pre class="Agda"><a id="52" class="Keyword">open</a> <a id="57" class="Keyword">import</a> <a id="64" href="Algebra.html" class="Module">Algebra</a> <a id="72" class="Keyword">using</a> <a id="78" class="Symbol">(</a><a id="79" href="Algebra.Structures.html#2810" class="Record">IsMonoid</a><a id="87" class="Symbol">)</a>
<a id="89" class="Keyword">open</a> <a id="94" class="Keyword">import</a> <a id="101" href="Data.List.html" class="Module">Data.List</a> <a id="111" class="Keyword">using</a> <a id="117" class="Symbol">(</a><a id="118" href="Agda.Builtin.List.html#147" class="Datatype">List</a><a id="122" class="Symbol">)</a>
<a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="Data.Maybe.html" class="Module">Data.Maybe</a> <a id="147" class="Keyword">using</a> <a id="153" class="Symbol">(</a><a id="154" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a><a id="159" class="Symbol">;</a><a id="160" href="Data.Maybe.Base.html#1641" class="Function">fromMaybe</a><a id="169" class="Symbol">)</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="192" class="Keyword">using</a> <a id="198" class="Symbol">(</a><a id="199" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="200" class="Symbol">)</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="Data.String.html" class="Module">Data.String</a> <a id="226" class="Keyword">using</a> <a id="232" class="Symbol">(</a><a id="233" href="Agda.Builtin.String.html#335" class="Postulate">String</a><a id="239" class="Symbol">;</a><a id="240" href="Data.String.Base.html#2118" class="Function">tail</a><a id="244" class="Symbol">)</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="Data.Vec.html" class="Module">Data.Vec</a> <a id="267" class="Keyword">using</a> <a id="273" class="Symbol">(</a><a id="274" href="Data.Vec.Base.html#1007" class="Datatype">Vec</a><a id="277" class="Symbol">)</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="329" class="Keyword">using</a> <a id="335" class="Symbol">(</a><a id="336" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="339" class="Symbol">)</a>

<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="Utils.Reflection.html" class="Module">Utils.Reflection</a> <a id="371" class="Keyword">using</a> <a id="377" class="Symbol">(</a><a id="378" href="Utils.Reflection.html#2691" class="Function">defDec</a><a id="384" class="Symbol">;</a><a id="385" href="Utils.Reflection.html#3082" class="Function">defShow</a><a id="392" class="Symbol">;</a><a id="393" href="Utils.Reflection.html#3450" class="Function">defListConstructors</a><a id="412" class="Symbol">)</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="RawU.html" class="Module">RawU</a> <a id="431" class="Keyword">using</a> <a id="437" class="Symbol">(</a><a id="438" href="RawU.html#7584" class="Datatype">TmCon</a><a id="443" class="Symbol">)</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="Builtin.html" class="Module">Builtin</a> <a id="465" class="Keyword">using</a> <a id="471" class="Symbol">(</a><a id="472" href="Builtin.html#1212" class="Datatype">Builtin</a><a id="479" class="Symbol">;</a><a id="480" href="Builtin.html#14096" class="Function">arity</a><a id="485" class="Symbol">)</a>
<a id="487" class="Keyword">open</a> <a id="492" class="Keyword">import</a> <a id="499" href="Untyped.CEK.html" class="Module">Untyped.CEK</a> <a id="511" class="Keyword">using</a> <a id="517" class="Symbol">(</a><a id="518" href="Untyped.CEK.html#1224" class="Datatype">Value</a><a id="523" class="Symbol">)</a>
</pre>
We will represent costs with Naturals. In the implementation `SatInt` is used, (integers that don't overflow, but saturate). 
As long as the budget is less than the maxInt then the result should be the same.

<pre class="Agda"><a id="CostingNat"></a><a id="743" href="Cost.Base.html#743" class="Function">CostingNat</a> <a id="754" class="Symbol">:</a> <a id="756" href="Agda.Primitive.html#388" class="Primitive">Set</a> 
<a id="761" href="Cost.Base.html#743" class="Function">CostingNat</a> <a id="772" class="Symbol">=</a> <a id="774" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
</pre>
We define one constructor for each possible type of node in a UPLC term.

<pre class="Agda"><a id="859" class="Keyword">data</a> <a id="StepKind"></a><a id="864" href="Cost.Base.html#864" class="Datatype">StepKind</a> <a id="873" class="Symbol">:</a> <a id="875" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="879" class="Keyword">where</a> 
    <a id="StepKind.BConst"></a><a id="890" href="Cost.Base.html#890" class="InductiveConstructor">BConst</a> 
      <a id="StepKind.BVar"></a><a id="904" href="Cost.Base.html#904" class="InductiveConstructor">BVar</a>
      <a id="StepKind.BLamAbs"></a><a id="915" href="Cost.Base.html#915" class="InductiveConstructor">BLamAbs</a>
      <a id="StepKind.BApply"></a><a id="929" href="Cost.Base.html#929" class="InductiveConstructor">BApply</a>
      <a id="StepKind.BDelay"></a><a id="942" href="Cost.Base.html#942" class="InductiveConstructor">BDelay</a>
      <a id="StepKind.BForce"></a><a id="955" href="Cost.Base.html#955" class="InductiveConstructor">BForce</a>
      <a id="StepKind.BBuiltin"></a><a id="968" href="Cost.Base.html#968" class="InductiveConstructor">BBuiltin</a> <a id="977" class="Comment">-- Cost of evaluating a Builtin AST node, not the function itself</a>
      <a id="StepKind.BConstr"></a><a id="1049" href="Cost.Base.html#1049" class="InductiveConstructor">BConstr</a> 
      <a id="StepKind.BCase"></a><a id="1064" href="Cost.Base.html#1064" class="InductiveConstructor">BCase</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="Cost.Base.html#864" class="Datatype">StepKind</a>
</pre>
We define a show function for StepKinds

<pre class="Agda"><a id="showStepKind&#39;"></a><a id="1131" href="Cost.Base.html#1131" class="Function">showStepKind&#39;</a> <a id="1145" class="Symbol">:</a> <a id="1147" href="Cost.Base.html#864" class="Datatype">StepKind</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="Agda.Builtin.String.html#335" class="Postulate">String</a> 
<a id="1166" class="Keyword">unquoteDef</a> <a id="1177" href="Cost.Base.html#1131" class="Function">showStepKind&#39;</a> <a id="1191" class="Symbol">=</a> <a id="1193" href="Utils.Reflection.html#3082" class="Function">defShow</a> <a id="1201" class="Symbol">(</a><a id="1202" class="Keyword">quote</a> <a id="1208" href="Cost.Base.html#864" class="Datatype">StepKind</a><a id="1216" class="Symbol">)</a> <a id="1218" href="Cost.Base.html#1131" class="Function">showStepKind&#39;</a> 

<a id="showStepKind"></a><a id="1234" href="Cost.Base.html#1234" class="Function">showStepKind</a> <a id="1247" class="Symbol">:</a> <a id="1249" href="Cost.Base.html#864" class="Datatype">StepKind</a> <a id="1258" class="Symbol">→</a> <a id="1260" href="Agda.Builtin.String.html#335" class="Postulate">String</a> 
<a id="1268" href="Cost.Base.html#1234" class="Function">showStepKind</a> <a id="1281" href="Cost.Base.html#1281" class="Bound">s</a> <a id="1283" class="Symbol">=</a> <a id="1285" href="Data.Maybe.Base.html#1641" class="Function">fromMaybe</a> <a id="1295" class="String">&quot;&quot;</a> <a id="1298" class="Symbol">(</a><a id="1299" href="Data.String.Base.html#2118" class="Function">tail</a> <a id="1304" class="Symbol">(</a><a id="1305" href="Cost.Base.html#1131" class="Function">showStepKind&#39;</a> <a id="1319" href="Cost.Base.html#1281" class="Bound">s</a><a id="1320" class="Symbol">))</a>   
</pre>
and a list of constructors names

<pre class="Agda"><a id="stepKindList"></a><a id="1370" href="Cost.Base.html#1370" class="Function">stepKindList</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1390" href="Cost.Base.html#864" class="Datatype">StepKind</a>
<a id="1399" class="Keyword">unquoteDef</a> <a id="1410" href="Cost.Base.html#1370" class="Function">stepKindList</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="Utils.Reflection.html#3450" class="Function">defListConstructors</a> <a id="1445" class="Symbol">(</a><a id="1446" class="Keyword">quote</a> <a id="1452" href="Cost.Base.html#864" class="Datatype">StepKind</a><a id="1460" class="Symbol">)</a> <a id="1462" href="Cost.Base.html#1370" class="Function">stepKindList</a> 
</pre>
## Recording expenditure

The following data structure is used to define the categories for which we
record expenditure.

<pre class="Agda"><a id="1608" class="Keyword">data</a> <a id="ExBudgetCategory"></a><a id="1613" href="Cost.Base.html#1613" class="Datatype">ExBudgetCategory</a> <a id="1630" class="Symbol">:</a> <a id="1632" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1636" class="Keyword">where</a>
      <a id="1648" class="Comment">-- Cost of Evaluating a machine step</a>
    <a id="ExBudgetCategory.BStep"></a><a id="1689" href="Cost.Base.html#1689" class="InductiveConstructor">BStep</a>       <a id="1701" class="Symbol">:</a> <a id="1703" href="Cost.Base.html#864" class="Datatype">StepKind</a> <a id="1712" class="Symbol">→</a> <a id="1714" href="Cost.Base.html#1613" class="Datatype">ExBudgetCategory</a>

     <a id="1737" class="Comment">-- Cost of evaluating a fully applied builtin function</a>
    <a id="ExBudgetCategory.BBuiltinApp"></a><a id="1796" href="Cost.Base.html#1796" class="InductiveConstructor">BBuiltinApp</a> <a id="1808" class="Symbol">:</a> <a id="1810" class="Symbol">(</a><a id="1811" href="Cost.Base.html#1811" class="Bound">b</a> <a id="1813" class="Symbol">:</a> <a id="1815" href="Builtin.html#1212" class="Datatype">Builtin</a><a id="1822" class="Symbol">)</a> <a id="1824" class="Symbol">→</a> <a id="1826" href="Data.Vec.Base.html#1007" class="Datatype">Vec</a> <a id="1830" href="Untyped.CEK.html#1224" class="Datatype">Value</a> <a id="1836" class="Symbol">(</a><a id="1837" href="Builtin.html#14096" class="Function">arity</a> <a id="1843" href="Cost.Base.html#1811" class="Bound">b</a><a id="1844" class="Symbol">)</a> <a id="1846" class="Symbol">→</a> <a id="1848" href="Cost.Base.html#1613" class="Datatype">ExBudgetCategory</a>  

    <a id="1872" class="Comment">-- Startup Cost</a>
    <a id="ExBudgetCategory.BStartup"></a><a id="1892" href="Cost.Base.html#1892" class="InductiveConstructor">BStartup</a>    <a id="1904" class="Symbol">:</a> <a id="1906" href="Cost.Base.html#1613" class="Datatype">ExBudgetCategory</a>
</pre>
## Machine Parameters

The CEK machine is parameterised by the following machine parameters.

<pre class="Agda"><a id="2026" class="Keyword">record</a> <a id="MachineParameters"></a><a id="2033" href="Cost.Base.html#2033" class="Record">MachineParameters</a> <a id="2051" class="Symbol">(</a><a id="2052" href="Cost.Base.html#2052" class="Bound">Cost</a> <a id="2057" class="Symbol">:</a> <a id="2059" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2062" class="Symbol">)</a> <a id="2064" class="Symbol">:</a> <a id="2066" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="2070" class="Keyword">where</a>
    <a id="2080" class="Keyword">field</a>
      <a id="MachineParameters.cekMachineCost"></a><a id="2092" href="Cost.Base.html#2092" class="Field">cekMachineCost</a> <a id="2107" class="Symbol">:</a> <a id="2109" href="Cost.Base.html#1613" class="Datatype">ExBudgetCategory</a> <a id="2126" class="Symbol">→</a> <a id="2128" href="Cost.Base.html#2052" class="Bound">Cost</a>
      <a id="MachineParameters.ε"></a><a id="2139" href="Cost.Base.html#2139" class="Field">ε</a> <a id="2141" class="Symbol">:</a> <a id="2143" href="Cost.Base.html#2052" class="Bound">Cost</a>
      <a id="MachineParameters._∙_"></a><a id="2154" href="Cost.Base.html#2154" class="Field Operator">_∙_</a> <a id="2158" class="Symbol">:</a> <a id="2160" href="Cost.Base.html#2052" class="Bound">Cost</a> <a id="2165" class="Symbol">→</a> <a id="2167" href="Cost.Base.html#2052" class="Bound">Cost</a> <a id="2172" class="Symbol">→</a> <a id="2174" href="Cost.Base.html#2052" class="Bound">Cost</a>
      <a id="MachineParameters.costMonoid"></a><a id="2185" href="Cost.Base.html#2185" class="Field">costMonoid</a> <a id="2196" class="Symbol">:</a> <a id="2198" href="Algebra.Structures.html#2810" class="Record">IsMonoid</a> <a id="2207" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a> <a id="2211" href="Cost.Base.html#2154" class="Field Operator">_∙_</a> <a id="2215" href="Cost.Base.html#2139" class="Field">ε</a>

    <a id="MachineParameters.startupCost"></a><a id="2222" href="Cost.Base.html#2222" class="Function">startupCost</a> <a id="2234" class="Symbol">:</a> <a id="2236" href="Cost.Base.html#2052" class="Bound">Cost</a> 
    <a id="2246" href="Cost.Base.html#2222" class="Function">startupCost</a> <a id="2258" class="Symbol">=</a> <a id="2260" href="Cost.Base.html#2092" class="Field">cekMachineCost</a> <a id="2275" href="Cost.Base.html#1892" class="InductiveConstructor">BStartup</a>
</pre>