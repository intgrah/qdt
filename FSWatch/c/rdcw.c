#include <lean/lean.h>

#if defined(_WIN32)

#include <stdio.h>
#include <windows.h>

static inline lean_obj_res lean_mk_string_from_wchar(const WCHAR *wstr,
                                                     DWORD byteLen) {
  int charLen = byteLen / sizeof(WCHAR);
  int utf8Len =
      WideCharToMultiByte(CP_UTF8, 0, wstr, charLen, NULL, 0, NULL, NULL);
  if (utf8Len == 0)
    return lean_mk_string("");
  char *utf8 = (char *)malloc(utf8Len + 1);
  WideCharToMultiByte(CP_UTF8, 0, wstr, charLen, utf8, utf8Len, NULL, NULL);
  utf8[utf8Len] = '\0';
  lean_obj_res result = lean_mk_string(utf8);
  free(utf8);
  return result;
}

LEAN_EXPORT lean_obj_res fswatch_rdcw_open(b_lean_obj_arg path,
                                           lean_obj_arg world) {
  const char *pathStr = lean_string_cstr(path);
  int wlen = MultiByteToWideChar(CP_UTF8, 0, pathStr, -1, NULL, 0);
  WCHAR *wpath = (WCHAR *)malloc(wlen * sizeof(WCHAR));
  MultiByteToWideChar(CP_UTF8, 0, pathStr, -1, wpath, wlen);

  HANDLE h = CreateFileW(wpath, FILE_LIST_DIRECTORY,
                         FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                         NULL, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, NULL);
  free(wpath);

  if (h == INVALID_HANDLE_VALUE) {
    DWORD err = GetLastError();
    char msg[128];
    snprintf(msg, sizeof(msg), "CreateFileW failed: %lu", err);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
  }
  return lean_io_result_mk_ok(lean_box((size_t)h));
}

LEAN_EXPORT lean_obj_res fswatch_rdcw_close(size_t h, lean_obj_arg world) {
  CloseHandle((HANDLE)h);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fswatch_rdcw_read(size_t h, uint8_t watchSubTree,
                                           uint32_t filter,
                                           lean_obj_arg world) {
  BYTE buffer[16384];
  DWORD bytesReturned = 0;

  BOOL success = ReadDirectoryChangesW((HANDLE)h, buffer, sizeof(buffer),
                                       watchSubTree ? TRUE : FALSE, filter,
                                       &bytesReturned, NULL, NULL);

  if (!success) {
    DWORD err = GetLastError();
    char msg[128];
    snprintf(msg, sizeof(msg), "ReadDirectoryChangesW failed: %lu", err);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
  }

  lean_obj_res events = lean_mk_empty_array();
  if (bytesReturned == 0) {
    return lean_io_result_mk_ok(events);
  }

  FILE_NOTIFY_INFORMATION *fni = (FILE_NOTIFY_INFORMATION *)buffer;
  for (;;) {
    lean_obj_res event = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(event, 0, lean_usize_to_nat((size_t)fni->Action));
    lean_ctor_set(
        event, 1,
        lean_mk_string_from_wchar(fni->FileName, fni->FileNameLength));
    events = lean_array_push(events, event);

    if (fni->NextEntryOffset == 0)
      break;
    fni = (FILE_NOTIFY_INFORMATION *)((BYTE *)fni + fni->NextEntryOffset);
  }

  return lean_io_result_mk_ok(events);
}

LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_FILE_NAME(void) {
  return FILE_NOTIFY_CHANGE_FILE_NAME;
}
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_DIR_NAME(void) {
  return FILE_NOTIFY_CHANGE_DIR_NAME;
}
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_ATTRIBUTES(void) {
  return FILE_NOTIFY_CHANGE_ATTRIBUTES;
}
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_SIZE(void) {
  return FILE_NOTIFY_CHANGE_SIZE;
}
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_LAST_WRITE(void) {
  return FILE_NOTIFY_CHANGE_LAST_WRITE;
}
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_SECURITY(void) {
  return FILE_NOTIFY_CHANGE_SECURITY;
}

LEAN_EXPORT uint32_t fswatch_FILE_ACTION_ADDED(void) {
  return FILE_ACTION_ADDED;
}
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_REMOVED(void) {
  return FILE_ACTION_REMOVED;
}
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_MODIFIED(void) {
  return FILE_ACTION_MODIFIED;
}
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_RENAMED_OLD_NAME(void) {
  return FILE_ACTION_RENAMED_OLD_NAME;
}
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_RENAMED_NEW_NAME(void) {
  return FILE_ACTION_RENAMED_NEW_NAME;
}

#else

#define PLATFORM_ERROR                                                         \
  lean_io_result_mk_error(lean_mk_io_user_error(                               \
      lean_mk_string("ReadDirectoryChangesW is only available on Windows")))

LEAN_EXPORT lean_obj_res fswatch_rdcw_open(b_lean_obj_arg path,
                                           lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_rdcw_close(size_t h, lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_rdcw_read(size_t h, uint8_t watchSubTree,
                                           uint32_t filter,
                                           lean_obj_arg world) {
  return PLATFORM_ERROR;
}

LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_FILE_NAME(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_DIR_NAME(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_ATTRIBUTES(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_SIZE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_LAST_WRITE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_NOTIFY_CHANGE_SECURITY(void) { return 0; }

LEAN_EXPORT uint32_t fswatch_FILE_ACTION_ADDED(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_REMOVED(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_MODIFIED(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_RENAMED_OLD_NAME(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_FILE_ACTION_RENAMED_NEW_NAME(void) { return 0; }

#endif
