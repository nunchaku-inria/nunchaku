# Howto

### Make a release

- udpate the repository itself
  * `git checkout stable`
  * `git merge master` to merge changes
  * edit `_oasis` to update version, etc.
  * `oasis setup`
  * `git commit --amend` to update the commit
  * `git tag 0.42`
  * `git push origin stable --tags`

- make an archive:
  * tar.gz: `git archive --prefix=nunchaku/ 0.42 -o nunchaku-0.42.tar.gz`
  * zip: `git archive --prefix=nunchaku/ 0.42 -o nunchaku-0.42.zip`

- upload the archive on gforge, write some release notes, send a mail.
