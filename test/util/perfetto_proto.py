#!/usr/bin/env python3
# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
#
# Writer for the Perfetto protobuf trace format. The subset needed for tracks,
# slices and counters is small enough to encode here directly, so this needs only
# the standard library.
#
# A trace is a bare stream of length delimited TracePacket messages. One record
# is the tag byte 0x0a (`Trace.packet`, field 1, wire type 2), a varint length,
# then the packet. Nothing wraps the stream, which is why concatenating two
# trace files gives one valid trace, and why a second producer can be merged in
# later as long as it picks uuids from a different range.
#
# Field numbers are from perfetto/trace/trace.proto and are the one thing here
# that has to stay in step with upstream. They are stable, and readers skip
# fields they do not know, so a newer Perfetto still reads what this writes.
#
#   TracePacket        timestamp=8, trusted_packet_sequence_id=10,
#                      track_event=11, track_descriptor=60
#   TrackEvent         type=9, track_uuid=11, name=23, counter_value=30,
#                      flow_ids=47, terminating_flow_ids=48
#   TrackDescriptor    uuid=1, name=2, parent_uuid=5, counter=8, description=14
#   CounterDescriptor  unit_name=6
#
#   TrackEvent.Type    1 slice begin, 2 slice end, 3 instant, 4 counter
#
# Note that `track_event` in TracePacket and `track_uuid` in TrackEvent are both
# field 11. They are different messages, so there is no conflict, but the two
# are easy to mix up when editing.

import struct

# TrackEvent.Type
TYPE_SLICE_BEGIN = 1
TYPE_SLICE_END = 2
TYPE_INSTANT = 3
TYPE_COUNTER = 4

# One writer, one sequence. Perfetto only needs this to be constant within a
# trace; the value itself carries no meaning for us.
SEQUENCE_ID = 1


def _varint(value):
    if value < 0:
        raise ValueError(f"varint cannot encode {value}")
    out = bytearray()
    while True:
        byte = value & 0x7F
        value >>= 7
        out.append(byte | (0x80 if value else 0))
        if not value:
            return bytes(out)


def _tag(field, wire):
    return _varint((field << 3) | wire)


# Tags are constant, so they are built once here.
_T_PACKET = _tag(1, 2)          # Trace.packet
_T_TIMESTAMP = _tag(8, 0)       # TracePacket.timestamp
_T_SEQ = _tag(10, 0)            # TracePacket.trusted_packet_sequence_id
_T_TRACK_EVENT = _tag(11, 2)    # TracePacket.track_event
_T_TRACK_DESC = _tag(60, 2)     # TracePacket.track_descriptor
_T_TE_TYPE = _tag(9, 0)         # TrackEvent.type
_T_TE_TRACK = _tag(11, 0)       # TrackEvent.track_uuid
_T_TE_NAME = _tag(23, 2)        # TrackEvent.name
_T_TE_COUNTER = _tag(30, 0)     # TrackEvent.counter_value
_T_TE_DCOUNTER = _tag(44, 1)    # TrackEvent.double_counter_value

# The two fixed event prefixes, and the sequence id suffix every packet carries.
_SEQ_SUFFIX = _T_SEQ + _varint(SEQUENCE_ID)
_EV_SLICE_BEGIN = _T_TE_TYPE + _varint(TYPE_SLICE_BEGIN) + _T_TE_TRACK
_EV_SLICE_END = _T_TE_TYPE + _varint(TYPE_SLICE_END) + _T_TE_TRACK
_EV_INSTANT = _T_TE_TYPE + _varint(TYPE_INSTANT) + _T_TE_TRACK
_EV_COUNTER = _T_TE_TYPE + _varint(TYPE_COUNTER) + _T_TE_TRACK


def _uint(field, value):
    return _tag(field, 0) + _varint(value)


def _int64(field, value):
    # protobuf sign extends int64 to ten bytes, so a negative counter value goes
    # out as the unsigned two's complement pattern
    return _tag(field, 0) + _varint(value & 0xFFFFFFFFFFFFFFFF)


def _bytes(field, raw):
    return _tag(field, 2) + _varint(len(raw)) + raw


def _string(field, text):
    return _bytes(field, text.encode())


def _double(field, value):
    return _tag(field, 1) + struct.pack("<d", value)


class TraceWriter:
    """Writes a .pftrace to an open binary file.

    Tracks are declared first and are referred to by uuid afterwards. Uuids only
    have to be unique inside one trace, so `uuid_base` lets a second producer
    take a range that will not collide when the two traces are concatenated.
    """

    def __init__(self, handle, uuid_base=1):
        self._w = handle
        self._next_uuid = uuid_base

    def _packet(self, body):
        body += _SEQ_SUFFIX
        self._w.write(_T_PACKET + _varint(len(body)) + body)

    def _event(self, ts, body):
        """A TracePacket carrying a TrackEvent. The hot path: on a long trace
        this runs once per counter sample and twice per frame."""
        body = _T_TIMESTAMP + _varint(ts) + _T_TRACK_EVENT + \
            _varint(len(body)) + body + _SEQ_SUFFIX
        self._w.write(_T_PACKET + _varint(len(body)) + body)

    def _uuid(self):
        uuid = self._next_uuid
        self._next_uuid += 1
        return uuid

    def track(self, name, parent=None, description=None):
        """Declare a track for slices and instant events. Returns its uuid."""
        uuid = self._uuid()
        desc = _uint(1, uuid) + _string(2, name)
        if parent is not None:
            desc += _uint(5, parent)
        if description:
            desc += _string(14, description)
        self._packet(_bytes(60, desc))
        return uuid

    def counter_track(self, name, parent=None, unit_name=None):
        """Declare a counter track. The empty CounterDescriptor is what marks
        the track as a counter, so it is written even with no unit."""
        uuid = self._uuid()
        counter = _string(6, unit_name) if unit_name else b""
        desc = _uint(1, uuid) + _string(2, name) + _bytes(8, counter)
        if parent is not None:
            desc += _uint(5, parent)
        self._packet(_bytes(60, desc))
        return uuid

    def slice_begin(self, track, ts, name):
        raw = name.encode()
        self._event(ts, _EV_SLICE_BEGIN + _varint(track) + _T_TE_NAME
                    + _varint(len(raw)) + raw)

    def slice_end(self, track, ts):
        self._event(ts, _EV_SLICE_END + _varint(track))

    def instant(self, track, ts, name):
        raw = name.encode()
        self._event(ts, _EV_INSTANT + _varint(track) + _T_TE_NAME
                    + _varint(len(raw)) + raw)

    def counter(self, track, ts, value):
        self._event(ts, _EV_COUNTER + _varint(track) + _T_TE_COUNTER
                    + _varint(int(value) & 0xFFFFFFFFFFFFFFFF))

    def counter_float(self, track, ts, value):
        """A counter sample that is not a whole number, IPC being the obvious
        one. Perfetto picks the type from which field is present."""
        self._event(ts, _EV_COUNTER + _varint(track) + _T_TE_DCOUNTER
                    + struct.pack("<d", value))
