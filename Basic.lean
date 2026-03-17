-- def hello := "world"

import Lean
open Lean Widget

structure GetTypeParams where
  name : Name
  pos : Lsp.Position
  deriving Server.RpcEncodable

@[widget_module]
def helloWidget : Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      const punctuation = props.punctuation
      const pair = props.pair
      return React.createElement('p', {}, 'Hello ' + name + punctuation + ' ' + JSON.stringify(pair))
    }"

#check ConstantInfo

open Server RequestM in
@[server_rpc_method]
def getType (params : GetTypeParams) : RequestM (RequestTask CodeWithInfos) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      let name ← resolveGlobalConstNoOverloadCore params.name
      let c ← try getConstInfo name
        catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
      match c with
        | ConstantInfo.thmInfo t => Widget.ppExprTagged t.value
        | _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩

@[widget_module]
def checkWidget : Widget.Module where
  javascript := "
import * as React from 'react';
const e = React.createElement;
import { useRpcSession, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';

export default function(props) {
  const rs = useRpcSession()
  const [name, setName] = React.useState('th1')

  const st = useAsync(() =>
    rs.call('getType', { name }), [name, rs])

  const type = st.state === 'resolved' ? st.value && e(InteractiveCode, {fmt: st.value})
    : st.state === 'rejected' ? e('p', null, mapRpcError(st.error).message)
    : e('p', null, 'Loading..')
  const onChange = (event) => { setName(event.target.value) }
  return e('div', null,
    e('input', { value: name, onChange }), ' : ', type)
}
"

theorem th1 (h : p ∧ q) : p := h.left

#widget checkWidget with { name := "th1", pos := ⟨0,0⟩ : GetTypeParams}

structure mypair where
  fst : String
  snd : Nat
  deriving Server.RpcEncodable

structure HelloWidgetProps where
  name? : Option String := none
  punctuation : String
  pair : mypair
  deriving Server.RpcEncodable

#widget helloWidget with { name? := "th1", punctuation := "?", pair := {fst := "hello", snd := 0} : HelloWidgetProps }
