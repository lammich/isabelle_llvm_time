; Generated by Isabelle/LLVM-shallow
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"



declare i8* @isabelle_llvm_calloc(i64, i64)


define void @LLVM_DS_Array_arrayset(i32* %dst, i32 %c, i32 %n) {

  start:
    br label %while_start

  while_start:
    %i = phi i32 [ %x1, %while_body ], [ 0, %start ]
    %x = icmp ult i32 %i, %n
    br i1 %x, label %while_body, label %while_end

  while_body:
    %p = getelementptr i32, i32* %dst, i32 %i
    store i32 %c, i32* %p
    %x1 = add i32 %i, 1
    br label %while_start

  while_end:
    ret void
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_set_impl(i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x2, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x2, 1
    %x3 = call i1 @IICF_Indexed_Array_List_ial_contains_impl (i32 %x, { { i32, i32* }, i32* } %a1)
    br i1 %x3, label %then, label %else

  then:
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_change_key_impl (i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2)
    br label %ctd_if

  else:
    %x5 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_insert_impl (i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2)
    br label %ctd_if

  ctd_if:
    %x6 = phi { { { i32, i32* }, i32* }, i32* } [ %x5, %else ], [ %x4, %then ]
    ret { { { i32, i32* }, i32* }, i32* } %x6
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_exch_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1, i32 %x2) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %x3 = sub i32 %x1, 1
    %xa = sub i32 %x2, 1
    %xb = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_swap_impl ({ { i32, i32* }, i32* } %a1, i32 %x3, i32 %xa)
    %xc = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %xb, 0
    %x4 = insertvalue { { { i32, i32* }, i32* }, i32* } %xc, i32* %a2, 1
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1) {

  start:
    %x2 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } zeroinitializer, { { { i32, i32* }, i32* }, i32* } %x, 0
    %x3 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x2, i32 %x1, 1
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl_f_06579412 ({ { { { i32, i32* }, i32* }, i32* }, i32 } %x3)
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1) {

  start:
    %x2 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } zeroinitializer, { { { i32, i32* }, i32* }, i32* } %x, 0
    %x3 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x2, i32 %x1, 1
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl_f_06575890 ({ { { { i32, i32* }, i32* }, i32* }, i32 } %x3)
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define i32* @LLVM_DS_NArray_narray_new_init(i32 %n, i32 %c) {

  start:
    %tmp = icmp eq i32 %n, 0
    br i1 %tmp, label %then, label %else

  then:
    br label %ctd_if

  else:
    %a = zext i32 %n to i64
    %t = getelementptr i32, i32* null, i64 1
    %b = ptrtoint i32* %t to i64
    %d = call i8* @isabelle_llvm_calloc (i64 %a, i64 %b)
    %x = bitcast i8* %d to i32*
    br label %ctd_if

  ctd_if:
    %r = phi i32* [ %x, %else ], [ null, %then ]
    call void @LLVM_DS_Array_arrayset (i32* %r, i32 %c, i32 %n)
    ret i32* %r
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_empty_impl(i32 %x) {

  start:
    %x1 = call i32* @LLVM_DS_NArray_narray_new_init (i32 %x, i32 zeroinitializer)
    %xa = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_empty_impl (i32 %x)
    %xb = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %xa, 0
    %x2 = insertvalue { { { i32, i32* }, i32* }, i32* } %xb, i32* %x1, 1
    ret { { { i32, i32* }, i32* }, i32* } %x2
}

define i32 @IICF_Impl_Heapmap_hm_index_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %x2 = getelementptr i32, i32* %a2a, i32 %x1
    %xa = load i32, i32* %x2
    %x3 = add i32 %xa, 1
    ret i32 %x3
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_append_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1, i32 %x2) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %x3 = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_append_impl ({ { i32, i32* }, i32* } %a1, i32 %x1)
    %p = getelementptr i32, i32* %a2, i32 %x1
    store i32 %x2, i32* %p
    %xb = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %x3, 0
    %x4 = insertvalue { { { i32, i32* }, i32* }, i32* } %xb, i32* %a2, 1
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_insert_impl(i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x2, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x2, 1
    %x3 = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_append_impl ({ { i32, i32* }, i32* } %a1, i32 %x)
    %p = getelementptr i32, i32* %a2, i32 %x
    store i32 %x1, i32* %p
    %xb = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %x3, 0
    %xc = insertvalue { { { i32, i32* }, i32* }, i32* } %xb, i32* %a2, 1
    %a1a = extractvalue { { { i32, i32* }, i32* }, i32* } %xc, 0
    %a2a = extractvalue { { { i32, i32* }, i32* }, i32* } %xc, 1
    %a1b = extractvalue { { i32, i32* }, i32* } %a1a, 0
    %a2b = extractvalue { { i32, i32* }, i32* } %a1a, 1
    %a1c = extractvalue { i32, i32* } %a1b, 0
    %a2c = extractvalue { i32, i32* } %a1b, 1
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl ({ { { i32, i32* }, i32* }, i32* } %xc, i32 %a1c)
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_remove_impl(i32 %x, { { { i32, i32* }, i32* }, i32* } %x1) {

  start:
    %x2 = call i32 @IICF_Impl_Heapmap_hm_index_impl ({ { { i32, i32* }, i32* }, i32* } %x1, i32 %x)
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %a1b = extractvalue { i32, i32* } %a1a, 0
    %a2b = extractvalue { i32, i32* } %a1a, 1
    %xb = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_exch_impl ({ { { i32, i32* }, i32* }, i32* } %x1, i32 %x2, i32 %a1b)
    %a1c = extractvalue { { { i32, i32* }, i32* }, i32* } %xb, 0
    %a2c = extractvalue { { { i32, i32* }, i32* }, i32* } %xb, 1
    %a1d = extractvalue { { i32, i32* }, i32* } %a1c, 0
    %a2d = extractvalue { { i32, i32* }, i32* } %a1c, 1
    %a1e = extractvalue { i32, i32* } %a1d, 0
    %a2e = extractvalue { i32, i32* } %a1d, 1
    %xd = sub i32 %a1e, 1
    %a1f = extractvalue { { i32, i32* }, i32* } %a1c, 0
    %a2f = extractvalue { { i32, i32* }, i32* } %a1c, 1
    %a1g = extractvalue { i32, i32* } %a1f, 0
    %a2g = extractvalue { i32, i32* } %a1f, 1
    %xe = getelementptr i32, i32* %a2g, i32 %xd
    %xf = load i32, i32* %xe
    %xg = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_butlast_impl ({ { i32, i32* }, i32* } %a1c)
    %xh = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %xg, 0
    %xi = insertvalue { { { i32, i32* }, i32* }, i32* } %xh, i32* %a2c, 1
    %xj = icmp ne i32 %x2, %a1b
    br i1 %xj, label %then, label %else

  then:
    %x3 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_repair_impl ({ { { i32, i32* }, i32* }, i32* } %xi, i32 %x2)
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %x4 = phi { { { i32, i32* }, i32* }, i32* } [ %xi, %else ], [ %x3, %then ]
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_repair_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1) {

  start:
    %x2 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl ({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1)
    %x3 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x1)
    ret { { { i32, i32* }, i32* }, i32* } %x3
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_update_impl({ { { i32, i32* }, i32* }, i32* } %x, i32 %x1, i32 %x2) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %x3 = sub i32 %x1, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %a1b = extractvalue { i32, i32* } %a1a, 0
    %a2b = extractvalue { i32, i32* } %a1a, 1
    %xa = getelementptr i32, i32* %a2b, i32 %x3
    %xb = load i32, i32* %xa
    %p = getelementptr i32, i32* %a2, i32 %xb
    store i32 %x2, i32* %p
    %xd = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %a1, 0
    %x4 = insertvalue { { { i32, i32* }, i32* }, i32* } %xd, i32* %a2, 1
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } @IICF_Impl_Heapmap_hm_pop_min_impl({ { { i32, i32* }, i32* }, i32* } %x) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %bi = sub i32 1, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %a1b = extractvalue { i32, i32* } %a1a, 0
    %a2b = extractvalue { i32, i32* } %a1a, 1
    %xa = getelementptr i32, i32* %a2b, i32 %bi
    %xaa = load i32, i32* %xa
    %a1c = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %bia = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %xb = getelementptr i32, i32* %bia, i32 %xaa
    %xc = load i32, i32* %xb
    %a1d = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2c = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %a1e = extractvalue { { i32, i32* }, i32* } %a1d, 0
    %a2d = extractvalue { { i32, i32* }, i32* } %a1d, 1
    %a1f = extractvalue { i32, i32* } %a1e, 0
    %a2e = extractvalue { i32, i32* } %a1e, 1
    %xe = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_exch_impl ({ { { i32, i32* }, i32* }, i32* } %x, i32 1, i32 %a1f)
    %a1g = extractvalue { { { i32, i32* }, i32* }, i32* } %xe, 0
    %a2f = extractvalue { { { i32, i32* }, i32* }, i32* } %xe, 1
    %a1h = extractvalue { { i32, i32* }, i32* } %a1g, 0
    %a2g = extractvalue { { i32, i32* }, i32* } %a1g, 1
    %a1i = extractvalue { i32, i32* } %a1h, 0
    %a2h = extractvalue { i32, i32* } %a1h, 1
    %xga = sub i32 %a1i, 1
    %a1j = extractvalue { { i32, i32* }, i32* } %a1g, 0
    %a2i = extractvalue { { i32, i32* }, i32* } %a1g, 1
    %a1k = extractvalue { i32, i32* } %a1j, 0
    %a2j = extractvalue { i32, i32* } %a1j, 1
    %xh = getelementptr i32, i32* %a2j, i32 %xga
    %xj = load i32, i32* %xh
    %xk = call { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_butlast_impl ({ { i32, i32* }, i32* } %a1g)
    %xl = insertvalue { { { i32, i32* }, i32* }, i32* } zeroinitializer, { { i32, i32* }, i32* } %xk, 0
    %xm = insertvalue { { { i32, i32* }, i32* }, i32* } %xl, i32* %a2f, 1
    %xna = icmp ne i32 %a1f, 1
    br i1 %xna, label %then, label %else

  then:
    %xoa = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl ({ { { i32, i32* }, i32* }, i32* } %xm, i32 1)
    %xp = insertvalue { i32, i32 } zeroinitializer, i32 %xaa, 0
    %xq = insertvalue { i32, i32 } %xp, i32 %xc, 1
    %xpa = insertvalue { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } zeroinitializer, { i32, i32 } %xq, 0
    %x1 = insertvalue { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } %xpa, { { { i32, i32* }, i32* }, i32* } %xoa, 1
    br label %ctd_if

  else:
    %xo = insertvalue { i32, i32 } zeroinitializer, i32 %xaa, 0
    %xp1 = insertvalue { i32, i32 } %xo, i32 %xc, 1
    %xoa1 = insertvalue { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } zeroinitializer, { i32, i32 } %xp1, 0
    %x2 = insertvalue { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } %xoa1, { { { i32, i32* }, i32* }, i32* } %xm, 1
    br label %ctd_if

  ctd_if:
    %x3 = phi { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } [ %x2, %else ], [ %x1, %then ]
    ret { { i32, i32 }, { { { i32, i32* }, i32* }, i32* } } %x3
}

define i1 @IICF_Impl_Heapmap_hm_is_empty_impl({ { { i32, i32* }, i32* }, i32* } %x) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %a1b = extractvalue { i32, i32* } %a1a, 0
    %a2b = extractvalue { i32, i32* } %a1a, 1
    %x1 = icmp eq i32 %a1b, 0
    ret i1 %x1
}

define { i32, i32 } @IICF_Impl_Heapmap_hm_peek_min_impl({ { { i32, i32* }, i32* }, i32* } %x) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %bi = sub i32 1, 1
    %a1a = extractvalue { { i32, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { i32, i32* }, i32* } %a1, 1
    %a1b = extractvalue { i32, i32* } %a1a, 0
    %a2b = extractvalue { i32, i32* } %a1a, 1
    %x1 = getelementptr i32, i32* %a2b, i32 %bi
    %xa = load i32, i32* %x1
    %a1c = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 0
    %bia = extractvalue { { { i32, i32* }, i32* }, i32* } %x, 1
    %xb = getelementptr i32, i32* %bia, i32 %xa
    %xc = load i32, i32* %xb
    %xd = insertvalue { i32, i32 } zeroinitializer, i32 %xa, 0
    %x2 = insertvalue { i32, i32 } %xd, i32 %xc, 1
    ret { i32, i32 } %x2
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_change_key_impl(i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2) {

  start:
    %x3 = call i32 @IICF_Impl_Heapmap_hm_index_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x)
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_update_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x3, i32 %x1)
    %x5 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_repair_impl ({ { { i32, i32* }, i32* }, i32* } %x4, i32 %x3)
    ret { { { i32, i32* }, i32* }, i32* } %x5
}

define i32 @IICF_Impl_Heapmap_hm_the_lookup_impl(i32 %x, { { { i32, i32* }, i32* }, i32* } %x1) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 0
    %bia = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 1
    %x2 = getelementptr i32, i32* %bia, i32 %x
    %x3 = load i32, i32* %x2
    ret i32 %x3
}

define { i32, i32* } @IICF_MS_Array_List_marl_butlast_impl({ i32, i32* } %x) {

  start:
    %a1 = extractvalue { i32, i32* } %x, 0
    %a2 = extractvalue { i32, i32* } %x, 1
    %x1 = sub i32 %a1, 1
    %xa = insertvalue { i32, i32* } zeroinitializer, i32 %x1, 0
    %x2 = insertvalue { i32, i32* } %xa, i32* %a2, 1
    ret { i32, i32* } %x2
}

define { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_swap_impl({ { i32, i32* }, i32* } %x, i32 %x1, i32 %x2) {

  start:
    %a1 = extractvalue { { i32, i32* }, i32* } %x, 0
    %a2 = extractvalue { { i32, i32* }, i32* } %x, 1
    %a1a = extractvalue { i32, i32* } %a1, 0
    %a2a = extractvalue { i32, i32* } %a1, 1
    %x3 = getelementptr i32, i32* %a2a, i32 %x1
    %xa = load i32, i32* %x3
    %a1b = extractvalue { i32, i32* } %a1, 0
    %a2b = extractvalue { i32, i32* } %a1, 1
    %xb = getelementptr i32, i32* %a2b, i32 %x2
    %xc = load i32, i32* %xb
    %a1c = extractvalue { i32, i32* } %a1, 0
    %a2c = extractvalue { i32, i32* } %a1, 1
    %p = getelementptr i32, i32* %a2c, i32 %x1
    store i32 %xc, i32* %p
    %xe = insertvalue { i32, i32* } zeroinitializer, i32 %a1c, 0
    %xf = insertvalue { i32, i32* } %xe, i32* %a2c, 1
    %a1d = extractvalue { i32, i32* } %xf, 0
    %a2d = extractvalue { i32, i32* } %xf, 1
    %pa = getelementptr i32, i32* %a2d, i32 %x2
    store i32 %xa, i32* %pa
    %xh = insertvalue { i32, i32* } zeroinitializer, i32 %a1d, 0
    %xi = insertvalue { i32, i32* } %xh, i32* %a2d, 1
    %pb = getelementptr i32, i32* %a2, i32 %xc
    store i32 %x1, i32* %pb
    %d = icmp eq i32 -1, %x1
    br i1 %d, label %then, label %else

  then:
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %pc = getelementptr i32, i32* %a2, i32 %xa
    store i32 %x2, i32* %pc
    %da = icmp eq i32 -1, %x2
    br i1 %da, label %thena, label %elsea

  thena:
    br label %ctd_ifa

  elsea:
    br label %ctd_ifa

  ctd_ifa:
    %xj = insertvalue { { i32, i32* }, i32* } zeroinitializer, { i32, i32* } %xi, 0
    %x4 = insertvalue { { i32, i32* }, i32* } %xj, i32* %a2, 1
    ret { { i32, i32* }, i32* } %x4
}

define i1 @IICF_Impl_Heapmap_hm_contains_key_impl(i32 %x, { { { i32, i32* }, i32* }, i32* } %x1) {

  start:
    %a1 = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 0
    %a2 = extractvalue { { { i32, i32* }, i32* }, i32* } %x1, 1
    %x2 = call i1 @IICF_Indexed_Array_List_ial_contains_impl (i32 %x, { { i32, i32* }, i32* } %a1)
    ret i1 %x2
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_decrease_key_impl(i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2) {

  start:
    %x3 = call i32 @IICF_Impl_Heapmap_hm_index_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x)
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_update_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x3, i32 %x1)
    %x5 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl ({ { { i32, i32* }, i32* }, i32* } %x4, i32 %x3)
    ret { { { i32, i32* }, i32* }, i32* } %x5
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_increase_key_impl(i32 %x, i32 %x1, { { { i32, i32* }, i32* }, i32* } %x2) {

  start:
    %x3 = call i32 @IICF_Impl_Heapmap_hm_index_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x)
    %x4 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_update_impl ({ { { i32, i32* }, i32* }, i32* } %x2, i32 %x3, i32 %x1)
    %x5 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl ({ { { i32, i32* }, i32* }, i32* } %x4, i32 %x3)
    ret { { { i32, i32* }, i32* }, i32* } %x5
}

define { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_empty_impl(i32 %x) {

  start:
    %x1 = call i32* @LLVM_DS_NArray_narray_new_init (i32 %x, i32 zeroinitializer)
    %xa = insertvalue { i32, i32* } zeroinitializer, i32 0, 0
    %xb = insertvalue { i32, i32* } %xa, i32* %x1, 1
    %r = call i32* @LLVM_DS_NArray_narray_new_init (i32 %x, i32 -1)
    %d = icmp eq i32 -1, -1
    br i1 %d, label %then, label %else

  then:
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %xc = insertvalue { { i32, i32* }, i32* } zeroinitializer, { i32, i32* } %xb, 0
    %x2 = insertvalue { { i32, i32* }, i32* } %xc, i32* %r, 1
    ret { { i32, i32* }, i32* } %x2
}

define { i32, i32* } @IICF_MS_Array_List_marl_push_back_impl({ i32, i32* } %x, i32 %x1) {

  start:
    %a1 = extractvalue { i32, i32* } %x, 0
    %a2 = extractvalue { i32, i32* } %x, 1
    %x2 = add i32 %a1, 1
    %p = getelementptr i32, i32* %a2, i32 %a1
    store i32 %x1, i32* %p
    %xb = insertvalue { i32, i32* } zeroinitializer, i32 %x2, 0
    %x3 = insertvalue { i32, i32* } %xb, i32* %a2, 1
    ret { i32, i32* } %x3
}

define { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_append_impl({ { i32, i32* }, i32* } %x, i32 %x1) {

  start:
    %a1 = extractvalue { { i32, i32* }, i32* } %x, 0
    %a2 = extractvalue { { i32, i32* }, i32* } %x, 1
    %a1a = extractvalue { i32, i32* } %a1, 0
    %a2a = extractvalue { i32, i32* } %a1, 1
    %xa = call { i32, i32* } @IICF_MS_Array_List_marl_push_back_impl ({ i32, i32* } %a1, i32 %x1)
    %p = getelementptr i32, i32* %a2, i32 %x1
    store i32 %a1a, i32* %p
    %d = icmp eq i32 -1, %a1a
    br i1 %d, label %then, label %else

  then:
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %xb = insertvalue { { i32, i32* }, i32* } zeroinitializer, { i32, i32* } %xa, 0
    %x2 = insertvalue { { i32, i32* }, i32* } %xb, i32* %a2, 1
    ret { { i32, i32* }, i32* } %x2
}

define { { i32, i32* }, i32* } @IICF_Indexed_Array_List_ial_butlast_impl({ { i32, i32* }, i32* } %x) {

  start:
    %a1 = extractvalue { { i32, i32* }, i32* } %x, 0
    %a2 = extractvalue { { i32, i32* }, i32* } %x, 1
    %a1a = extractvalue { i32, i32* } %a1, 0
    %a2a = extractvalue { i32, i32* } %a1, 1
    %xa = sub i32 %a1a, 1
    %a1b = extractvalue { i32, i32* } %a1, 0
    %a2b = extractvalue { i32, i32* } %a1, 1
    %xb = getelementptr i32, i32* %a2b, i32 %xa
    %xc = load i32, i32* %xb
    %xd = call { i32, i32* } @IICF_MS_Array_List_marl_butlast_impl ({ i32, i32* } %a1)
    %p = getelementptr i32, i32* %a2, i32 %xc
    store i32 -1, i32* %p
    %d = icmp eq i32 -1, -1
    br i1 %d, label %then, label %else

  then:
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %xe = insertvalue { { i32, i32* }, i32* } zeroinitializer, { i32, i32* } %xd, 0
    %x1 = insertvalue { { i32, i32* }, i32* } %xe, i32* %a2, 1
    ret { { i32, i32* }, i32* } %x1
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl_f_06579412({ { { { i32, i32* }, i32* }, i32* }, i32 } %x) {

  start:
    %a1 = extractvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x, 0
    %a2 = extractvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x, 1
    %a1a = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %a1b = extractvalue { { i32, i32* }, i32* } %a1a, 0
    %a2b = extractvalue { { i32, i32* }, i32* } %a1a, 1
    %a1c = extractvalue { i32, i32* } %a1b, 0
    %a2c = extractvalue { i32, i32* } %a1b, 1
    %xba = udiv i32 %a1c, 2
    %xc = icmp sle i32 %a2, %xba
    br i1 %xc, label %then, label %else

  then:
    %xd = mul i32 2, %a2
    %a1d = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2d = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bia = sub i32 %xd, 1
    %a1e = extractvalue { { i32, i32* }, i32* } %a1d, 0
    %a2e = extractvalue { { i32, i32* }, i32* } %a1d, 1
    %a1f = extractvalue { i32, i32* } %a1e, 0
    %a2f = extractvalue { i32, i32* } %a1e, 1
    %xea = getelementptr i32, i32* %a2f, i32 %bia
    %xf = load i32, i32* %xea
    %a1g = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bib = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xg = getelementptr i32, i32* %bib, i32 %xf
    %xh = load i32, i32* %xg
    %a1h = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2g = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %a1i = extractvalue { { i32, i32* }, i32* } %a1h, 0
    %a2h = extractvalue { { i32, i32* }, i32* } %a1h, 1
    %a1j = extractvalue { i32, i32* } %a1i, 0
    %a2i = extractvalue { i32, i32* } %a1i, 1
    %xj = icmp slt i32 %xd, %a1j
    br i1 %xj, label %thena, label %elsea

  thena:
    %xka = add i32 %xd, 1
    %a1k = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2j = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bic = sub i32 %xka, 1
    %a1l = extractvalue { { i32, i32* }, i32* } %a1k, 0
    %a2k = extractvalue { { i32, i32* }, i32* } %a1k, 1
    %a1m = extractvalue { i32, i32* } %a1l, 0
    %a2l = extractvalue { i32, i32* } %a1l, 1
    %xla = getelementptr i32, i32* %a2l, i32 %bic
    %xm = load i32, i32* %xla
    %a1n = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bid = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xn = getelementptr i32, i32* %bid, i32 %xm
    %xo = load i32, i32* %xn
    %xp = icmp slt i32 %xo, %xh
    br i1 %xp, label %thenb, label %elseb

  thenb:
    br label %ctd_ifb

  elseb:
    br label %ctd_ifb

  ctd_ifb:
    %x1 = phi i32 [ %xd, %elseb ], [ %xka, %thenb ]
    br label %ctd_ifa

  elsea:
    br label %ctd_ifa

  ctd_ifa:
    %xk = phi i32 [ %xd, %elsea ], [ %x1, %ctd_ifb ]
    %a1k1 = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2j1 = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bic1 = sub i32 %xk, 1
    %a1l1 = extractvalue { { i32, i32* }, i32* } %a1k1, 0
    %a2k1 = extractvalue { { i32, i32* }, i32* } %a1k1, 1
    %a1m1 = extractvalue { i32, i32* } %a1l1, 0
    %a2l1 = extractvalue { i32, i32* } %a1l1, 1
    %xla1 = getelementptr i32, i32* %a2l1, i32 %bic1
    %xm1 = load i32, i32* %xla1
    %a1n1 = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bid1 = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xn1 = getelementptr i32, i32* %bid1, i32 %xm1
    %xo1 = load i32, i32* %xn1
    %a1o = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2m = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bie = sub i32 %a2, 1
    %a1p = extractvalue { { i32, i32* }, i32* } %a1o, 0
    %a2n = extractvalue { { i32, i32* }, i32* } %a1o, 1
    %a1q = extractvalue { i32, i32* } %a1p, 0
    %a2o = extractvalue { i32, i32* } %a1p, 1
    %xpa = getelementptr i32, i32* %a2o, i32 %bie
    %xq = load i32, i32* %xpa
    %a1r = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bif = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xr = getelementptr i32, i32* %bif, i32 %xq
    %xs = load i32, i32* %xr
    %xt = icmp slt i32 %xo1, %xs
    br i1 %xt, label %thenc, label %elsec

  thenc:
    %xu = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_exch_impl ({ { { i32, i32* }, i32* }, i32* } %a1, i32 %a2, i32 %xk)
    %xv = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } zeroinitializer, { { { i32, i32* }, i32* }, i32* } %xu, 0
    %x2 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %xv, i32 %xk, 1
    %x3 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_sink_impl_f_06579412 ({ { { { i32, i32* }, i32* }, i32* }, i32 } %x2)
    br label %ctd_ifc

  elsec:
    br label %ctd_ifc

  ctd_ifc:
    %x4 = phi { { { i32, i32* }, i32* }, i32* } [ %a1, %elsec ], [ %x3, %thenc ]
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %x5 = phi { { { i32, i32* }, i32* }, i32* } [ %a1, %else ], [ %x4, %ctd_ifc ]
    ret { { { i32, i32* }, i32* }, i32* } %x5
}

define { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl_f_06575890({ { { { i32, i32* }, i32* }, i32* }, i32 } %x) {

  start:
    %a1 = extractvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x, 0
    %a2 = extractvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %x, 1
    %xaa = icmp slt i32 1, %a2
    br i1 %xaa, label %then, label %else

  then:
    %xba = udiv i32 %a2, 2
    %a1a = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2a = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bia = sub i32 %xba, 1
    %a1b = extractvalue { { i32, i32* }, i32* } %a1a, 0
    %a2b = extractvalue { { i32, i32* }, i32* } %a1a, 1
    %a1c = extractvalue { i32, i32* } %a1b, 0
    %a2c = extractvalue { i32, i32* } %a1b, 1
    %xca = getelementptr i32, i32* %a2c, i32 %bia
    %xd = load i32, i32* %xca
    %a1d = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bib = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xe = getelementptr i32, i32* %bib, i32 %xd
    %xf = load i32, i32* %xe
    %a1e = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %a2d = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %bic = sub i32 %a2, 1
    %a1f = extractvalue { { i32, i32* }, i32* } %a1e, 0
    %a2e = extractvalue { { i32, i32* }, i32* } %a1e, 1
    %a1g = extractvalue { i32, i32* } %a1f, 0
    %a2f = extractvalue { i32, i32* } %a1f, 1
    %xga = getelementptr i32, i32* %a2f, i32 %bic
    %xh = load i32, i32* %xga
    %a1h = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 0
    %bid = extractvalue { { { i32, i32* }, i32* }, i32* } %a1, 1
    %xi = getelementptr i32, i32* %bid, i32 %xh
    %xj = load i32, i32* %xi
    %xk = icmp sle i32 %xf, %xj
    %xla = add i1 %xk, 1
    br i1 %xla, label %thena, label %elsea

  thena:
    %xma = udiv i32 %a2, 2
    %xn = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_exch_impl ({ { { i32, i32* }, i32* }, i32* } %a1, i32 %a2, i32 %xma)
    %xoa = udiv i32 %a2, 2
    %xp = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } zeroinitializer, { { { i32, i32* }, i32* }, i32* } %xn, 0
    %x1 = insertvalue { { { { i32, i32* }, i32* }, i32* }, i32 } %xp, i32 %xoa, 1
    %x2 = call { { { i32, i32* }, i32* }, i32* } @IICF_Impl_Heapmap_hm_swim_impl_f_06575890 ({ { { { i32, i32* }, i32* }, i32* }, i32 } %x1)
    br label %ctd_ifa

  elsea:
    br label %ctd_ifa

  ctd_ifa:
    %x3 = phi { { { i32, i32* }, i32* }, i32* } [ %a1, %elsea ], [ %x2, %thena ]
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    %x4 = phi { { { i32, i32* }, i32* }, i32* } [ %a1, %else ], [ %x3, %ctd_ifa ]
    ret { { { i32, i32* }, i32* }, i32* } %x4
}

define i1 @IICF_Indexed_Array_List_ial_contains_impl(i32 %x, { { i32, i32* }, i32* } %x1) {

  start:
    %a1 = extractvalue { { i32, i32* }, i32* } %x1, 0
    %a2 = extractvalue { { i32, i32* }, i32* } %x1, 1
    %x2 = getelementptr i32, i32* %a2, i32 %x
    %xa = load i32, i32* %x2
    %xb = icmp eq i32 -1, %xa
    %r = add i1 %xb, 1
    %d = icmp eq i32 -1, %xa
    br i1 %d, label %then, label %else

  then:
    br label %ctd_if

  else:
    br label %ctd_if

  ctd_if:
    ret i1 %r
}
