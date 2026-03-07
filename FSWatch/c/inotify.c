#include <lean/lean.h>

#if defined(__linux__) || defined(__FreeBSD__)

#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res fswatch_inotify_init(lean_obj_arg world) {
  int fd = inotify_init1(IN_NONBLOCK | IN_CLOEXEC);
  if (fd < 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(strerror(errno))));
  }
  return lean_io_result_mk_ok(lean_box((size_t)fd));
}

LEAN_EXPORT lean_obj_res fswatch_inotify_add_watch(uint32_t fd,
                                                   lean_obj_arg path,
                                                   uint32_t mask,
                                                   lean_obj_arg world) {
  const char *path_str = lean_string_cstr(path);
  int wd = inotify_add_watch((int)fd, path_str, mask);
  if (wd < 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(strerror(errno))));
  }
  return lean_io_result_mk_ok(lean_box((size_t)wd));
}

LEAN_EXPORT lean_obj_res fswatch_inotify_rm_watch(uint32_t fd, uint32_t wd,
                                                  lean_obj_arg world) {
  if (inotify_rm_watch((int)fd, (int)wd) < 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(strerror(errno))));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fswatch_inotify_close(uint32_t fd,
                                               lean_obj_arg world) {
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}

static lean_object *mk_raw_event(int32_t wd, uint32_t mask, uint32_t cookie,
                                 const char *name) {
  lean_object *obj = lean_alloc_ctor(0, 4, 0);
  lean_ctor_set(obj, 0, lean_usize_to_nat((size_t)wd));
  lean_ctor_set(obj, 1, lean_usize_to_nat((size_t)mask));
  lean_ctor_set(obj, 2, lean_usize_to_nat((size_t)cookie));
  lean_ctor_set(obj, 3, lean_mk_string(name ? name : ""));
  return obj;
}

LEAN_EXPORT lean_obj_res fswatch_inotify_read(uint32_t fd, lean_obj_arg world) {
  char buf[4096] __attribute__((aligned(__alignof__(struct inotify_event))));

  ssize_t len = read((int)fd, buf, sizeof(buf));
  if (len < 0) {
    if (errno == EAGAIN || errno == EWOULDBLOCK) {
      return lean_io_result_mk_ok(lean_mk_empty_array());
    }
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(strerror(errno))));
  }

  lean_object *arr = lean_mk_empty_array();

  char *ptr = buf;
  while (ptr < buf + len) {
    struct inotify_event *event = (struct inotify_event *)ptr;

    const char *name = (event->len > 0) ? event->name : "";
    lean_object *raw_event =
        mk_raw_event(event->wd, event->mask, event->cookie, name);
    arr = lean_array_push(arr, raw_event);

    ptr += sizeof(struct inotify_event) + event->len;
  }

  return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT uint32_t fswatch_IN_ACCESS(void) { return IN_ACCESS; }
LEAN_EXPORT uint32_t fswatch_IN_MODIFY(void) { return IN_MODIFY; }
LEAN_EXPORT uint32_t fswatch_IN_ATTRIB(void) { return IN_ATTRIB; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE_WRITE(void) { return IN_CLOSE_WRITE; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE_NOWRITE(void) { return IN_CLOSE_NOWRITE; }
LEAN_EXPORT uint32_t fswatch_IN_OPEN(void) { return IN_OPEN; }
LEAN_EXPORT uint32_t fswatch_IN_MOVED_FROM(void) { return IN_MOVED_FROM; }
LEAN_EXPORT uint32_t fswatch_IN_MOVED_TO(void) { return IN_MOVED_TO; }
LEAN_EXPORT uint32_t fswatch_IN_CREATE(void) { return IN_CREATE; }
LEAN_EXPORT uint32_t fswatch_IN_DELETE(void) { return IN_DELETE; }
LEAN_EXPORT uint32_t fswatch_IN_DELETE_SELF(void) { return IN_DELETE_SELF; }
LEAN_EXPORT uint32_t fswatch_IN_MOVE_SELF(void) { return IN_MOVE_SELF; }
LEAN_EXPORT uint32_t fswatch_IN_UNMOUNT(void) { return IN_UNMOUNT; }
LEAN_EXPORT uint32_t fswatch_IN_Q_OVERFLOW(void) { return IN_Q_OVERFLOW; }
LEAN_EXPORT uint32_t fswatch_IN_IGNORED(void) { return IN_IGNORED; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE(void) { return IN_CLOSE; }
LEAN_EXPORT uint32_t fswatch_IN_MOVE(void) { return IN_MOVE; }
LEAN_EXPORT uint32_t fswatch_IN_ISDIR(void) { return IN_ISDIR; }
LEAN_EXPORT uint32_t fswatch_IN_ALL_EVENTS(void) { return IN_ALL_EVENTS; }

#else

#define PLATFORM_ERROR                                                         \
  lean_io_result_mk_error(lean_mk_io_user_error(                               \
      lean_mk_string("inotify is only available on Linux/FreeBSD")))

LEAN_EXPORT lean_obj_res fswatch_inotify_init(lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_inotify_add_watch(uint32_t fd,
                                                   lean_obj_arg path,
                                                   uint32_t mask,
                                                   lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_inotify_rm_watch(uint32_t fd, uint32_t wd,
                                                  lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_inotify_close(uint32_t fd,
                                               lean_obj_arg world) {
  return PLATFORM_ERROR;
}
LEAN_EXPORT lean_obj_res fswatch_inotify_read(uint32_t fd, lean_obj_arg world) {
  return PLATFORM_ERROR;
}

LEAN_EXPORT uint32_t fswatch_IN_ACCESS(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_MODIFY(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_ATTRIB(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE_WRITE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE_NOWRITE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_OPEN(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_MOVED_FROM(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_MOVED_TO(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_CREATE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_DELETE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_DELETE_SELF(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_MOVE_SELF(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_UNMOUNT(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_Q_OVERFLOW(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_IGNORED(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_CLOSE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_MOVE(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_ISDIR(void) { return 0; }
LEAN_EXPORT uint32_t fswatch_IN_ALL_EVENTS(void) { return 0; }

#endif
