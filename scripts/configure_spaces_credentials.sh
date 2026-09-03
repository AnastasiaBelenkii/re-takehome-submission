#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o pipefail

credentials_dir=/root/.config/re-takehome
credentials_file="${credentials_dir}/spaces-credentials"
temporary_file=""
spaces_key=""
spaces_secret=""

cleanup() {
  unset spaces_key spaces_secret
  if [[ -n "${temporary_file}" && -f "${temporary_file}" ]]; then
    rm -- "${temporary_file}"
  fi
}
trap cleanup EXIT

install -d -m 700 "${credentials_dir}"

if [[ -e "${credentials_file}" ]]; then
  read -r -p "${credentials_file} already exists. Replace it? [y/N] " replace
  case "${replace}" in
    y|Y|yes|YES) ;;
    *) echo "Left the existing credential file unchanged."; exit 0 ;;
  esac
fi

read -r -p "Space name: " spaces_bucket
read -r -p "Region slug (for example nyc3): " spaces_region
read -r -s -p "Spaces access-key ID: " spaces_key
printf '\n'
read -r -s -p "Spaces secret key: " spaces_secret
printf '\n'

case "${spaces_bucket}" in
  *[!a-z0-9.-]*|'') echo "Invalid Space name." >&2; exit 1 ;;
esac

case "${spaces_region}" in
  *[!a-z0-9-]*|'') echo "Invalid region slug." >&2; exit 1 ;;
esac

if [[ -z "${spaces_key}" || -z "${spaces_secret}" ]]; then
  echo "The access-key ID and secret key cannot be empty." >&2
  exit 1
fi

umask 077
temporary_file=$(mktemp "${credentials_dir}/spaces-credentials.XXXXXX")
{
  printf 'SPACES_BUCKET=%s\n' "${spaces_bucket}"
  printf 'SPACES_REGION=%s\n' "${spaces_region}"
  printf 'SPACES_ENDPOINT=https://%s.digitaloceanspaces.com\n' "${spaces_region}"
  printf 'SPACES_ACCESS_KEY_ID=%s\n' "${spaces_key}"
  printf 'SPACES_SECRET_ACCESS_KEY=%s\n' "${spaces_secret}"
} > "${temporary_file}"
chmod 600 "${temporary_file}"
mv -- "${temporary_file}" "${credentials_file}"
temporary_file=""

echo "Saved Spaces credentials to ${credentials_file} with mode 600."
