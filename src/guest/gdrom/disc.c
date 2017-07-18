#include "guest/gdrom/disc.h"
#include "core/assert.h"
#include "core/string.h"
#include "guest/gdrom/cdi.h"
#include "guest/gdrom/gdi.h"
#include "guest/gdrom/iso.h"

int disc_find_file(struct disc *disc, const char *filename, int *fad,
                   int *len) {
  uint8_t tmp[0x10000];

  /* get the session for the main data track */
  struct session *session = disc_get_session(disc, 1);
  struct track *data_track = disc_get_track(disc, session->first_track);

  /* read primary volume descriptor */
  int read = disc_read_sectors(disc, data_track->fad + ISO_PVD_SECTOR, 1,
                               GD_SECTOR_ANY, GD_MASK_DATA, tmp, sizeof(tmp));
  if (!read) {
    return 0;
  }

  struct iso_pvd *pvd = (struct iso_pvd *)tmp;
  CHECK(pvd->type == 1);
  CHECK(memcmp(pvd->id, "CD001", 5) == 0);
  CHECK(pvd->version == 1);

  /* check root directory for the file
     FIXME recurse subdirectories */
  struct iso_dir *root = &pvd->root_directory_record;
  int root_len = root->size.le;
  int root_fad = GDROM_PREGAP + root->extent.le;
  read = disc_read_bytes(disc, root_fad, root_len, tmp, sizeof(tmp));
  if (!read) {
    return 0;
  }

  uint8_t *ptr = tmp;
  uint8_t *end = tmp + root_len;

  while (ptr < end) {
    struct iso_dir *dir = (struct iso_dir *)ptr;
    const char *name = (const char *)(ptr + sizeof(*dir));

    if (memcmp(name, filename, strlen(filename)) == 0) {
      break;
    }

    /* dir entries always begin on an even byte */
    ptr = (uint8_t *)name + dir->name_len;
    ptr = (uint8_t *)align_up((intptr_t)ptr, (intptr_t)2);
  }

  if (ptr == end) {
    return 0;
  }

  struct iso_dir *dir = (struct iso_dir *)ptr;
  *fad = GDROM_PREGAP + dir->extent.le;
  *len = dir->size.le;

  return 1;
}

int disc_read_bytes(struct disc *disc, int fad, int len, void *dst,
                    int dst_size) {
  CHECK_LE(len, dst_size);

  uint8_t tmp[DISC_MAX_SECTOR_SIZE];
  int rem = len;

  while (rem) {
    int n = disc->read_sectors(disc, fad, 1, GD_SECTOR_ANY, GD_MASK_DATA, tmp,
                               sizeof(tmp));
    CHECK(n);

    /* don't overrun */
    n = MIN(n, rem);
    memcpy(dst, tmp, n);

    rem -= n;
    dst += n;
    fad++;
  }

  return len;
}

int disc_read_sectors(struct disc *disc, int fad, int num_sectors,
                      int sector_fmt, int sector_mask, void *dst,
                      int dst_size) {
  return disc->read_sectors(disc, fad, num_sectors, sector_fmt, sector_mask,
                            dst, dst_size);
}

void disc_get_toc(struct disc *disc, int area, struct track **first_track,
                  struct track **last_track, int *leadin_fad,
                  int *leadout_fad) {
  disc->get_toc(disc, area, first_track, last_track, leadin_fad, leadout_fad);
}

struct track *disc_lookup_track(struct disc *disc, int fad) {
  int num_tracks = disc_get_num_tracks(disc);

  for (int i = 0; i < num_tracks; i++) {
    struct track *track = disc_get_track(disc, i);

    if (fad < track->fad) {
      continue;
    }

    if (i < num_tracks - 1) {
      struct track *next = disc_get_track(disc, i + 1);

      if (fad >= next->fad) {
        continue;
      }
    }

    return track;
  }

  return NULL;
}

struct track *disc_get_track(struct disc *disc, int n) {
  return disc->get_track(disc, n);
}

int disc_get_num_tracks(struct disc *disc) {
  return disc->get_num_tracks(disc);
}

struct session *disc_get_session(struct disc *disc, int n) {
  return disc->get_session(disc, n);
}

int disc_get_num_sessions(struct disc *disc) {
  return disc->get_num_sessions(disc);
}

void disc_destroy(struct disc *disc) {
  disc->destroy(disc);
}

int disc_get_format(struct disc *disc) {
  return disc->get_format(disc);
}

void disc_get_meta(struct disc *disc, struct disc_meta *meta) {
  struct session *session = disc_get_session(disc, 1);

  uint8_t tmp[DISC_MAX_SECTOR_SIZE];
  disc_read_sectors(disc, session->leadin_fad, 1, GD_SECTOR_ANY, GD_MASK_DATA,
                    tmp, sizeof(tmp));

  memcpy(meta, tmp, sizeof(*meta));
}

struct disc *disc_create(const char *filename) {
  if (strstr(filename, ".cdi")) {
    return cdi_create(filename);
  }

  if (strstr(filename, ".gdi")) {
    return gdi_create(filename);
  }

  return NULL;
}
