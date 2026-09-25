#!/usr/bin/env python3
"""Run a Magma script on the public Magma calculator (latest version) and
print its output. Reads the script from stdin (at most 50000 bytes)."""
import sys, time, urllib.parse, urllib.request, xml.etree.ElementTree as ET

URL = "https://magma.maths.usyd.edu.au/xml/calculator.xml"
UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"

src = sys.stdin.read()
if len(src.encode()) > 50000:
    sys.exit("input too large for the calculator (50000 bytes)")
data = urllib.parse.urlencode({"input": src}).encode()
req = urllib.request.Request(URL, data=data, headers={"User-Agent": UA})
with urllib.request.urlopen(req, timeout=120) as r:
    xml = r.read()
root = ET.fromstring(xml)
off = root.find("offline")
if off is not None and off.text:
    sys.exit("calculator offline: " + off.text)
h = root.find("headers")
if h is not None:
    info = {c.tag: c.text for c in h}
    print(f"[magma {info.get('version')} time {info.get('time')}]", file=sys.stderr)
for line in root.iter("line"):
    print(line.text or "")
time.sleep(2)  # be gentle with the public service
