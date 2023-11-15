/*
    Copyright (c) 2021 Arthur Paulino. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Arthur Paulino
*/

#include <lean/lean.h>
#include <mysql/mysql.h>
#include <string.h>

typedef struct mysql {
    MYSQL* connection;
    char       logged;
    int        status;
    int   buffer_size;
    int    buffer_pos;
    char*      buffer;
    char   has_result;
    MYSQL_RES* result;
} mysql;

static lean_external_class* g_mysql_external_class = NULL;

static const char* ERR_NOT_LOGGED = "Not logged in.";
static const char* ERR_ALRDY_LOGGED = "Already logged in. Try using 'close' first.";
static const char* ERR_CANT_INIT = "Failed to instantiate a connection with MySQL.";
static const char* ERR_NO_MEM = "Not enough memory to allocate buffer.";
static const char* ERR_INCR_BFFR = "Not enough memory. Try increasing the buffer size.";

static const char* INT = "i";
static const char* FLOAT = "f";
static const char* STRING = "s";

static const char* NULL_ = "NULL";

static const char* TYPE_SEP = "^^";
static const char* COL_SEP = "~~";
static const char* LINE_SEP = "¨¨";

static lean_object* mysql_box(mysql* m) {
    return lean_alloc_external(g_mysql_external_class, m);
}

static mysql* mysql_unbox(lean_object* o) {
    return (mysql*) (lean_get_external_data(o));
}

static lean_obj_res make_error(const char* err_msg) {
    return lean_mk_io_user_error(lean_mk_io_user_error(lean_mk_string(err_msg)));
}

static void close_connection(mysql* m) {
    m->logged = 0;
    mysql_free_result(m->result);
    mysql_close(m->connection);
}

static void mysql_finalizer(void* mysql_ptr) {
    mysql* m = (mysql*) mysql_ptr;
    close_connection(m);
    if (m->connection) {
        free(m->connection);
    }
    free(m->buffer);
    free(m);
}

static void noop_foreach(void* mod, b_lean_obj_arg fn) {}

static void query(mysql* m, const char* q) {
    m->status = mysql_query(m->connection, q);
    m->result = mysql_store_result(m->connection);
}

static char append_to_buffer(mysql* m, const char* s) {
    int size = strlen(s);
    if (m->buffer_size - m->buffer_pos < size + 1) {
        return 0;
    }
    memcpy(m->buffer + m->buffer_pos, s, size + 1);
    m->buffer_pos = m->buffer_pos + size;
    return 1;
}

static const char* type_to_str(int t) {
    switch (t) {
        case MYSQL_TYPE_TINY:
            return INT;
        case MYSQL_TYPE_SHORT:
            return INT;
        case MYSQL_TYPE_LONG:
            return INT;
        case MYSQL_TYPE_LONGLONG:
            return INT;
        case MYSQL_TYPE_INT24:
            return INT;
        case MYSQL_TYPE_DECIMAL:
            return FLOAT;
        case MYSQL_TYPE_FLOAT:
            return FLOAT;
        case MYSQL_TYPE_DOUBLE:
            return FLOAT;
        default:
            return STRING;
    }
}

// API

LEAN_EXPORT lean_obj_res lean_mysql_initialize() {
    g_mysql_external_class = lean_register_external_class(mysql_finalizer, noop_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_mysql_mk(uint64_t b) {
    mysql* m = (mysql*) malloc(sizeof(mysql));
    char* buffer = (char*)malloc(b);
    if (!buffer) {
        return make_error(ERR_NO_MEM);
    }
    m->connection = NULL;
    m->logged = 0;
    m->status = 0;
    m->buffer_size = b;
    m->buffer_pos = 0;
    m->buffer = buffer;
    m->has_result = 0;
    m->result = NULL;
    return lean_io_result_mk_ok(mysql_box(m));
}

LEAN_EXPORT lean_obj_res lean_mysql_set_buffer_size(b_lean_obj_arg m_, uint64_t b) {
    mysql* m = mysql_unbox(m_);
    char* buffer = (char*)malloc(b);
    if (!buffer) {
        return make_error(ERR_NO_MEM);
    }
    free(m->buffer);
    m->buffer = buffer;
    m->buffer_size = b;
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_mysql_version() {
    return lean_mk_string(mysql_get_client_info());
}

LEAN_EXPORT lean_obj_res lean_mysql_login(b_lean_obj_arg m_, b_lean_obj_arg h_, b_lean_obj_arg u_, b_lean_obj_arg p_) {
    mysql* m = mysql_unbox(m_);
    if (m->logged) {
        return make_error(ERR_ALRDY_LOGGED);
    }

    m->connection = mysql_init(NULL);
    if (!m->connection) {
        return make_error(ERR_CANT_INIT);
    }

    const char* h = lean_string_cstr(h_);
    const char* u = lean_string_cstr(u_);
    const char* p = lean_string_cstr(p_);
    MYSQL *connection_ret = mysql_real_connect(
        m->connection,
        h, u, p,
        NULL, 0, NULL, 0
    );

    if (!connection_ret) {
        return make_error(mysql_error(m->connection));
    }
    else {
        m->logged = 1;
        return lean_io_result_mk_ok(lean_box(0));
    }
}

LEAN_EXPORT lean_obj_res lean_mysql_run(b_lean_obj_arg m_, b_lean_obj_arg q_) {
    mysql* m = mysql_unbox(m_);
    if (!m->logged) {
        return make_error(ERR_NOT_LOGGED);
    }

    query(m, lean_string_cstr(q_));
    if (m->status) {
        return make_error(mysql_error(m->connection));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_mysql_process_query_result(b_lean_obj_arg m_) {
    mysql* m = mysql_unbox(m_);

    m->buffer_pos = 0;

    // encoding header
    int num_fields = mysql_num_fields(m->result);
    MYSQL_FIELD* field;

    for(int j = 0; j < num_fields; j++) {
        field = mysql_fetch_field(m->result);
        if (!append_to_buffer(m, field->name)) {
            return make_error(ERR_INCR_BFFR);
        }
        if (!append_to_buffer(m, TYPE_SEP)) {
            return make_error(ERR_INCR_BFFR);
        }
        if (!append_to_buffer(m, type_to_str(field->type))) {
            return make_error(ERR_INCR_BFFR);
        }
        if (j < num_fields - 1) {
            if (!append_to_buffer(m, COL_SEP)) {
                return make_error(ERR_INCR_BFFR);
            }
        }
    }
    if (!append_to_buffer(m, LINE_SEP)) {
        return make_error(ERR_INCR_BFFR);
    }

    // encoding data
    int num_rows = mysql_num_rows(m->result);
    MYSQL_ROW row;

    for (int i = 0; i < num_rows; i++) {
        row = mysql_fetch_row(m->result);
        for(int j = 0; j < num_fields; j++) {
            if (!append_to_buffer(m, row[j] ? row[j] : NULL_)) {
                return make_error(ERR_INCR_BFFR);
            }
            if (j < num_fields - 1) {
                if (!append_to_buffer(m, COL_SEP)) {
                    return make_error(ERR_INCR_BFFR);
                }
            }
        }
        if (i < num_rows - 1) {
            if (!append_to_buffer(m, LINE_SEP)) {
                return make_error(ERR_INCR_BFFR);
            }
        }
    }

    if (!append_to_buffer(m, "\0")) {
        return make_error(ERR_INCR_BFFR);
    }

    return lean_mk_string(m->buffer);
}

LEAN_EXPORT lean_obj_res lean_mysql_close(b_lean_obj_arg m_) {
    mysql* m = mysql_unbox(m_);
    close_connection(m);
    return lean_io_result_mk_ok(lean_box(0));
}
