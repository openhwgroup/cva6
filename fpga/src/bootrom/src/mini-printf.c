/*
 * The Minimal snprintf() implementation
 *
 * Copyright (c) 2013,2014 Michal Ludvig <michal@logix.cz>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the auhor nor the names of its contributors
 *       may be used to endorse or promote products derived from this software
 *       without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * ----
 *
 * This is a minimal snprintf() implementation optimised
 * for embedded systems with a very limited program memory.
 * snprintf() doesn't support _all_ the formatting
 * the glibc does but on the other hand is a lot smaller.
 * Here are some numbers from my STM32 project (.bin file size):
 *      no snprintf():      10768 bytes
 *      mini snprintf():    11420 bytes     (+  652 bytes)
 *      glibc snprintf():   34860 bytes     (+24092 bytes)
 * Wasting nearly 24kB of memory just for snprintf() on
 * a chip with 32kB flash is crazy. Use snprintf() instead.
 *
 */

#include <string.h>
#include <stdarg.h>
#include "mini-printf.h"
#include "uart.h"

static unsigned int
itoa(int value, unsigned int radix, unsigned int uppercase, unsigned int unsig,
	 char *buffer, unsigned int zero_pad)
{
	char	*pbuffer = buffer;
	int	negative = 0;
	unsigned int	i, len;

	/* No support for unusual radixes. */
	if (radix > 16)
		return 0;

	if (value < 0 && !unsig) {
		negative = 1;
		value = -value;
	}

	/* This builds the string back to front ... */
	do {
		int digit = value % radix;
		*(pbuffer++) = (digit < 10 ? '0' + digit : (uppercase ? 'A' : 'a') + digit - 10);
		value /= radix;
	} while (value > 0);

	for (i = (pbuffer - buffer); i < zero_pad; i++)
		*(pbuffer++) = '0';

	if (negative)
		*(pbuffer++) = '-';

	*(pbuffer) = '\0';

	/* ... now we reverse it (could do it recursively but will
	 * conserve the stack space) */
	len = (pbuffer - buffer);
	for (i = 0; i < len / 2; i++) {
		char j = buffer[i];
		buffer[i] = buffer[len-i-1];
		buffer[len-i-1] = j;
	}

	return len;
}

int
vsnprintf(char *buffer, size_t buffer_len, const char *fmt, va_list va)
{
	char *pbuffer = buffer;
	char bf[24];
	char ch;

	int _putc(char ch)
	{
		if ((unsigned int)((pbuffer - buffer) + 1) >= buffer_len)
			return 0;
		*(pbuffer++) = ch;
		*(pbuffer) = '\0';
		return 1;
	}

	int _puts(char *s, unsigned int len)
	{
		unsigned int i;

		if (buffer_len - (pbuffer - buffer) - 1 < len)
			len = buffer_len - (pbuffer - buffer) - 1;

		/* Copy to buffer */
		for (i = 0; i < len; i++)
			*(pbuffer++) = s[i];
		*(pbuffer) = '\0';

		return len;
	}

	while ((ch=*(fmt++))) {
		if ((unsigned int)((pbuffer - buffer) + 1) >= buffer_len)
			break;
		if (ch!='%')
			_putc(ch);
		else {
			char zero_pad = 0;
			char *ptr;
			unsigned int len;

			ch=*(fmt++);
                        if (ch == 'l')
                          ch=*(fmt++);

			/* Zero padding requested */
			if (ch=='0') {
				ch=*(fmt++);
				if (ch == '\0')
					goto end;
				if (ch >= '0' && ch <= '9')
					zero_pad = ch - '0';
				ch=*(fmt++);
			}

			switch (ch) {
				case 0:
					goto end;

				case 'u':
				case 'd':
					len = itoa(va_arg(va, unsigned int), 10, 0, (ch=='u'), bf, zero_pad);
					_puts(bf, len);
					break;

				case 'x':
				case 'X':
					len = itoa(va_arg(va, unsigned int), 16, (ch=='X'), 1, bf, zero_pad);
					_puts(bf, len);
					break;

				case 'c' :
					_putc((char)(va_arg(va, int)));
					break;

				case 'p':
                                        len = itoa(va_arg(va, size_t), 16, 0, 1, bf, zero_pad);
					_puts(bf, len);
					break;

				case 's' :
                                        ptr = (char *)(va_arg(va, size_t) & 0xFFFFFFFF); // a horrible hack
					_puts(ptr, strlen(ptr));
					break;

				default:
					_putc(ch);
					break;
			}
		}
	}
end:
	return pbuffer - buffer;
}


int snprintf(char* buffer, size_t buffer_len, const char *fmt, ...)
{
	int ret;
	va_list va;
	va_start(va, fmt);
	ret = vsnprintf(buffer, buffer_len, fmt, va);
	va_end(va);

	return ret;
}

int sprintf(char* buffer, const char *fmt, ...)
{
	int ret;
	va_list va;
	va_start(va, fmt);
	ret = vsnprintf(buffer, 256, fmt, va);
	va_end(va);

	return ret;
}

int printf (const char *fmt, ...)
{
  char buffer[256];
  va_list va;
  int rslt;
  va_start(va, fmt);
  rslt = vsnprintf(buffer, sizeof(buffer), fmt, va);
  va_end(va);
  print_uart(buffer);
  return rslt;
}
