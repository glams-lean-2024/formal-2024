// Lean compiler output
// Module: Formal2024.Tactics.tada
// Imports: Init Lean
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_tacticTada___closed__2;
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_tacticTada___closed__4;
static lean_object* l_tacticTada___closed__5;
lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_tacticTada___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(lean_object*);
static lean_object* l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1;
static lean_object* l_tacticTada___closed__1;
static lean_object* l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3;
LEAN_EXPORT lean_object* l_tacticTada;
static lean_object* _init_l_tacticTada___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticTada", 10);
return x_1;
}
}
static lean_object* _init_l_tacticTada___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticTada___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticTada___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tada", 4);
return x_1;
}
}
static lean_object* _init_l_tacticTada___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticTada___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticTada___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticTada___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticTada___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticTada() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticTada___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Goals accomplished 🎉", 23);
return x_1;
}
}
static lean_object* _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_tacticTada___closed__2;
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_isEmpty___rarg(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Elab_Term_reportUnsolvedGoals(x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg(x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3;
x_26 = 0;
x_27 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_27;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Formal2024_Tactics_tada(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_tacticTada___closed__1 = _init_l_tacticTada___closed__1();
lean_mark_persistent(l_tacticTada___closed__1);
l_tacticTada___closed__2 = _init_l_tacticTada___closed__2();
lean_mark_persistent(l_tacticTada___closed__2);
l_tacticTada___closed__3 = _init_l_tacticTada___closed__3();
lean_mark_persistent(l_tacticTada___closed__3);
l_tacticTada___closed__4 = _init_l_tacticTada___closed__4();
lean_mark_persistent(l_tacticTada___closed__4);
l_tacticTada___closed__5 = _init_l_tacticTada___closed__5();
lean_mark_persistent(l_tacticTada___closed__5);
l_tacticTada = _init_l_tacticTada();
lean_mark_persistent(l_tacticTada);
l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1 = _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1();
lean_mark_persistent(l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__1);
l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2 = _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2();
lean_mark_persistent(l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__2);
l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3 = _init_l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3();
lean_mark_persistent(l___aux__Formal2024__Tactics__tada______elabRules__tacticTada__1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
