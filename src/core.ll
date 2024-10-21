; external functions definitions

declare void @__tc_fail1(i64 %0, i64 %1, i64 %2) cold noreturn
declare void @__tc_fail_null(i64 %0) cold noreturn
declare i1 @__cmp_any({ i64, i64 } %0, { i64, i64 } %1)
declare nonnull noundef ptr @__allocm(i64 %0) allockind("alloc") "alloc-family"="__allocm" allocsize(0)
declare void @__freem(ptr %0, i64 %1) allockind("free") "alloc-family"="__allocm"

; simple values - no implicit casts, type tags must be exactly equal

define { i64, i64 } @.toany_simple(i64 %tag, i64 %payload) alwaysinline {
entry:
    %0 = insertvalue { i64, i64 } undef, i64 %tag, 0
    %1 = insertvalue { i64, i64 } %0, i64 %payload, 1
    ret { i64, i64 } %1
}

define i64 @.fromany_simple(i64 %tag, { i64, i64 } %val) alwaysinline {
entry:
    %0 = extractvalue { i64, i64 } %val, 0
    %1 = extractvalue { i64, i64 } %val, 1
    %2 = icmp eq i64 %0, %tag
    br i1 %2, label %success, label %fail
success:
    ret i64 %1
fail:
    tail call void @__tc_fail1(i64 %tag, i64 %0, i64 %1)
    unreachable
}

; nullable (option) values - must check the value

define { i64, i64 } @.toany_nullable(i64 %tag, i64 %payload) alwaysinline {
    ; if the value is null, use tag_null (3) instead)
    %1 = icmp eq i64 %payload, 0
    %2 = select i1 %1, i64 3, i64 %tag
    %3 = insertvalue { i64, i64 } undef, i64 %2, 0
    %4 = insertvalue { i64, i64 } %3, i64 %payload, 1
    ret { i64, i64 } %4
}

define i64 @.fromany_nullable(i64 %tag, { i64, i64 } %val) alwaysinline {
entry:
  %0 = extractvalue { i64, i64 } %val, 0
  %1 = extractvalue { i64, i64 } %val, 1
  %2 = icmp eq i64 %0, %tag
  br i1 %2, label %success, label %trynull
trynull:
  %3 = icmp eq i64 %0, 3
  br i1 %3, label %success, label %fail
success:
  %4 = phi i64 [ %1, %entry ], [ 0, %trynull ]
  ret i64 %4
fail:                                             ; preds = %trynull
  tail call void @__tc_fail1(i64 %tag, i64 %0, i64 %1)
  unreachable
}

define ptr @.unwrap_nullable(ptr %val, i64 %type) alwaysinline {
entry:
  %0 = icmp eq ptr %val, null
  br i1 %0, label %fail, label %success
success:
  ret ptr %val
fail:
  tail call void @__tc_fail_null(i64 %type)
  unreachable
}

attributes #0 = { cold noreturn }