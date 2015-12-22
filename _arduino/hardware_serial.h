/*
  hardware_serial.h - Hardware serial library for Wiring
  Copyright (c) 2006 Nicholas Zambetti.  All right reserved.

  This library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  This library is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA

  Modified 28 September 2010 by Mark Sproul
  Modified 14 August 2012 by Alarus
*/

#ifndef HardwareSerial_h
#define HardwareSerial_h

#include <inttypes.h>
#include <stdbool.h>
#include "wiring_private.h"

struct ring_buffer;

// Define config for Serial.begin(baud, config);
#define SERIAL_5N1 0x00
#define SERIAL_6N1 0x02
#define SERIAL_7N1 0x04
#define SERIAL_8N1 0x06
#define SERIAL_5N2 0x08
#define SERIAL_6N2 0x0A
#define SERIAL_7N2 0x0C
#define SERIAL_8N2 0x0E
#define SERIAL_5E1 0x20
#define SERIAL_6E1 0x22
#define SERIAL_7E1 0x24
#define SERIAL_8E1 0x26
#define SERIAL_5E2 0x28
#define SERIAL_6E2 0x2A
#define SERIAL_7E2 0x2C
#define SERIAL_8E2 0x2E
#define SERIAL_5O1 0x30
#define SERIAL_6O1 0x32
#define SERIAL_7O1 0x34
#define SERIAL_8O1 0x36
#define SERIAL_5O2 0x38
#define SERIAL_6O2 0x3A
#define SERIAL_7O2 0x3C
#define SERIAL_8O2 0x3E

#if defined(USBCON) || defined(UBRRH) || defined(UBRR0H)
extern struct ring_buffer rx_buffer;
extern struct ring_buffer tx_buffer;
#endif

inline void c_sbi(volatile uint8_t *addr, uint8_t bit) {
  sbi(*((volatile uint8_t *) addr), bit);
}

inline void c_cbi(volatile uint8_t *addr, uint8_t bit) {
  cbi(*((volatile uint8_t *) addr), bit);
}

inline uint8_t c_rbi(volatile uint8_t *addr, uint8_t bit) {
  return (_SFR_BYTE(*((volatile uint8_t *) addr)) & _BV(bit));
}

void ringbuf_insert_nowait(unsigned char c, struct ring_buffer *buffer);
void ringbuf_insert_wait(unsigned char c, struct ring_buffer *buffer);
bool ringbuf_is_empty(struct ring_buffer *buffer);
unsigned int ringbuf_get_size(struct ring_buffer *buffer);
unsigned char ringbuf_peek(struct ring_buffer *buffer);
unsigned char ringbuf_remove(struct ring_buffer *buffer);
void ringbuf_clear(struct ring_buffer *buffer);

#endif
