#!/usr/bin/env python3
"""Verify the audit bibliography DOI inventory.

The default check is deterministic and offline.  ``--online`` additionally re-queries Crossref;
it is intentionally not part of the ordinary build because network availability is not a proof
assumption.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIBLIOGRAPHY = ROOT / "docs" / "AUDIT_BIBLIOGRAPHY.md"
SNAPSHOT = ROOT / "docs" / "AUDIT_DOI_METADATA.tsv"
DOI_LINK = re.compile(r"<https://doi\.org/([^>]+)>", re.IGNORECASE)


def normalized_doi(value: str) -> str:
    return value.strip().lower()


def normalized_text(value: str) -> str:
    return " ".join(value.casefold().split())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--online", action="store_true", help="re-query Crossref metadata")
    args = parser.parse_args()

    bibliography_dois = {
        normalized_doi(doi) for doi in DOI_LINK.findall(BIBLIOGRAPHY.read_text())
    }
    expected_fields = [
        "doi", "title", "authors", "container", "year", "volume", "pages", "crossref_url"
    ]
    with SNAPSHOT.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != expected_fields:
            print(f"ERROR metadata schema {reader.fieldnames!r} != {expected_fields!r}", file=sys.stderr)
            return 1
        rows = list(reader)

    snapshot_by_doi = {normalized_doi(row["doi"]): row for row in rows}
    if len(snapshot_by_doi) != len(rows):
        print("ERROR duplicate DOI in metadata snapshot", file=sys.stderr)
        return 1
    if bibliography_dois != set(snapshot_by_doi):
        print("ERROR bibliography/snapshot DOI mismatch", file=sys.stderr)
        print("  missing snapshot:", sorted(bibliography_dois - set(snapshot_by_doi)), file=sys.stderr)
        print("  stale snapshot:", sorted(set(snapshot_by_doi) - bibliography_dois), file=sys.stderr)
        return 1
    for doi, row in snapshot_by_doi.items():
        if not row["title"]:
            print(f"ERROR missing title for {doi}", file=sys.stderr)
            return 1
        expected_url = "https://doi.org/" + doi
        if row["crossref_url"].strip().casefold() != expected_url:
            print(
                f"ERROR Crossref URL/DOI mismatch for {doi}: {row['crossref_url']!r}",
                file=sys.stderr,
            )
            return 1

    if args.online:
        for doi, row in sorted(snapshot_by_doi.items()):
            url = "https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="")
            request = urllib.request.Request(
                url,
                headers={"User-Agent": "YangMillsDefinition-audit/1.0"},
            )
            with urllib.request.urlopen(request, timeout=30) as response:
                message = json.load(response)["message"]
            live = {
                "title": "; ".join(message.get("title", [])),
                "authors": "; ".join(
                    " ".join(filter(None, [author.get("given", ""), author.get("family", "")]))
                    for author in message.get("author", [])
                ),
                "container": "; ".join(message.get("container-title", [])),
                "year": str((message.get("published", {}).get("date-parts") or [[""]])[0][0]),
                "volume": str(message.get("volume", "")),
                "pages": str(message.get("page", "")),
                "crossref_url": str(message.get("URL", "")),
            }
            for field, live_value in live.items():
                saved_value = row[field]
                if field == "crossref_url":
                    agrees = live_value.strip().casefold() == saved_value.strip().casefold()
                else:
                    agrees = normalized_text(live_value) == normalized_text(saved_value)
                if not agrees:
                    print(
                        f"ERROR Crossref {field} drift for {doi}: "
                        f"{live_value!r} != {saved_value!r}",
                        file=sys.stderr,
                    )
                    return 1

    mode = "online Crossref" if args.online else "offline snapshot"
    print(f"PASS {mode}-verified {len(rows)} audit bibliography DOI record(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
